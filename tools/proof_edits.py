#!/usr/bin/env python3
"""Replace the proofs of chosen theorems, trying alternatives side by side and keeping what passes.

An edit is: in this module, replace everything after the `:=` that ends this theorem's statement by
this text. The statement itself is never touched. Edits are generated from the tables (a citation
of a copy the file already imports, or the text of the shortest proof of the same statement found
elsewhere), so they are guesses: each one has to compile and pass the equivalence check.

  tools/proof_edits.py citations  --out build/x/edits.jsonl [--form first|short] [--min-proof-tokens N]
  tools/proof_edits.py transplants --out build/x/edits.jsonl
  tools/proof_edits.py shorten     --out build/x/edits.jsonl    # shorten citations already recorded
  tools/proof_edits.py projections --out build/x/edits.jsonl [--min-parts N] [--min-nodes N]
                                                               # read long conjunctions by projection
  tools/proof_edits.py opaque-set  --out build/x/edits.jsonl [--min-nodes N]
                                                               # `clear_value x` after `set x := e with h`
  tools/proof_edits.py variants --edits E --work W [--single-from W/results.jsonl]
  tools/proof_edits.py choose   --edits E --work W            # after tools/batch_variants.py ran
  tools/proof_edits.py apply    --chosen W/chosen.jsonl [--expect W/final/sources.tsv [--drop-stale]]
                                                               # write the chosen edits into proof/src

Variants. For every module, `variants` writes the file with all its edits applied (variant `all`)
under W/v/all/. Files are always built from the accepted commit, never from the working tree.
tools/batch_variants.py compiles each variant and checks it. With --single-from, a module whose
`all` variant failed and has several edits gets one variant per edit (`e0`, `e1`, ...), and later
`combine` gets the ones that passed on their own. `choose` then keeps, per module, the passing
variant that removes the most, records exactly which edits it contains (W/chosen.jsonl), and
gathers its compiled files under W/final/new for the judge.

Because every file is rebuilt from the accepted commit and the edit list, applying the chosen
edits on another machine gives byte-identical files. `choose` records the checksum of each source
it kept (W/final/sources.tsv) and `apply --expect` refuses to write anything that differs from it.
"""
import argparse, collections, hashlib, json, os, re, shutil, subprocess, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C
import cone as CONE
import iface as IFACE
import cite_duplicates as CD

LONG = ' by first | exact @{c} | exact {c} | (intros; apply {c} <;> assumption)'
LONG_TOKENS = 18


def accepted_commit():
    state = C.accepted_state()
    return state['proof_commit'] if state else C.UPSTREAM_TAG


def texts_at(commit, modules):
    """Source of many modules at a commit of proof/, with one git process."""
    paths = ['src/' + m.replace('.', '/') + '.lean' for m in modules]
    req = ''.join(f'{commit}:{p}\n' for p in paths).encode()
    out = subprocess.run(['git', '-C', C.PROOF, 'cat-file', '--batch'], input=req, stdout=subprocess.PIPE,
                         check=True).stdout
    res, pos = {}, 0
    for m in modules:
        nl = out.index(b'\n', pos)
        header = out[pos:nl].split()
        if len(header) < 3:
            pos = nl + 1
            continue
        size = int(header[2])
        res[m] = out[nl + 1:nl + 1 + size].decode('utf-8')
        pos = nl + 1 + size + 1
    return res


def split_decl(text, lines, r):
    """-> (start of declaration, offset just after its `:=`, end of declaration) or None."""
    a = CD.offset(lines, r[0], r[1])
    b = CD.offset(lines, r[2], r[3])
    k = CD.statement_end(text[a:b])
    if k is None:
        return None
    return a, a + k, b


def apply_edits(text, edits):
    """Apply edits (dicts with first_line.. and body) to one file's accepted text. Returns the new text
    and the edits that could not be placed."""
    lines = text.split('\n')
    placed, failed = [], []
    for e in edits:
        if 'start' in e:                                  # an edit of one exact span inside a proof
            if hashlib.sha256(text[e['start']:e['end']].encode('utf-8')).hexdigest() != e['old_sha']:
                failed.append(e)
            else:
                placed.append((e['start'], e['end'], e['body']))
            continue
        s = split_decl(text, lines, (e['first_line'], e['first_col'], e['last_line'], e['last_col']))
        short = CD.user_name(e['theorem']).split('.')[-1]
        if s is None or short not in text[s[0]:s[1]]:
            failed.append(e)
            continue
        placed.append((s[1], s[2], e['body']))
    placed.sort(reverse=True)
    last = len(text) + 1
    for a, b, body in placed:
        if b > last:
            continue
        text = text[:a] + body + text[b:]
        last = a
    return text, failed


# ------------------------------------------------------------------ generating edits
def groups_of_copies(say):
    """Statements proved independently more than once: [(statement size, [declaration index])], with the
    graph, cone membership, source ranges, and the size of each theorem's auxiliaries."""
    overlay_consts = os.path.join(C.DATA_OVERLAY, 'consts.tsv')
    g = CONE.load_graph(C.DATA_BASE, overlay_consts if os.path.exists(overlay_consts) else None, (), say)
    by_name = CONE.find_names(g, set(C.TARGETS))
    cone = CONE.reach(g, [by_name[t] for t in C.TARGETS])
    ranges = CD.load_ranges(g.patched)
    groups = collections.defaultdict(list)
    for i in range(g.n):
        if cone[i] and g.kinds[i] == 'thm' and not IFACE.AUX.search(g.names[i]):
            groups[(g.thash[i], g.tsize[i])].append(i)
    ve, vo = g.v_edges, g.v_off
    indep = []
    for key, members in groups.items():
        if len(members) < 2:
            continue
        mset = set(members)
        roots = [i for i in members if not ((set(ve[vo[i]:vo[i + 1]]) & mset) - {i})]
        if len(roots) > 1:
            indep.append((key[1], roots))
    aux = collections.Counter()
    for i in range(g.n):
        if cone[i] and IFACE.AUX.search(g.names[i]):
            nm = g.names[i]
            aux[(g.mods[i], nm[:IFACE.AUX.search(nm).start()])] += g.tsize[i] + g.vsize[i]
    return g, ranges, indep, aux


def import_closures(g, holders):
    """closure[m] as a bit set over `holders` (module indices), and a topological position per module."""
    modnames = g.modnames
    midx = {m: k for k, m in enumerate(modnames)}
    imports = [[midx[x] for x in imps if x in midx] for imps in g.mod_imports]
    bit = {m: k for k, m in enumerate(sorted(holders))}
    order, state = [], bytearray(len(modnames))
    for root in range(len(modnames)):
        if state[root]:
            continue
        stack = [(root, iter(imports[root]))]
        state[root] = 1
        while stack:
            m, it = stack[-1]
            for i in it:
                if not state[i]:
                    state[i] = 1
                    stack.append((i, iter(imports[i])))
                    break
            else:
                stack.pop()
                order.append(m)
    topo = [0] * len(modnames)
    for k, m in enumerate(order):
        topo[m] = k
    closure = [0] * len(modnames)
    for m in order:
        c = 0
        for i in imports[m]:
            c |= closure[i]
            b = bit.get(i)
            if b is not None:
                c |= 1 << b
        closure[m] = c
    return closure, bit, topo


def gen(kind, out, form, min_tokens):
    """Write edits: `citations` (a copy the file already imports) or `transplants` (the text of the
    shortest proof of the same statement, for copies that cannot cite)."""
    t0 = time.time()

    def say(msg):
        print(f'{msg}  [{time.time() - t0:.0f}s]', flush=True)

    g, ranges, indep, aux = groups_of_copies(say)
    closure, bit, topo = import_closures(g, {g.mods[i] for _, roots in indep for i in roots})
    modnames = g.modnames
    need = sorted({modnames[g.mods[i]] for _, roots in indep for i in roots})
    text = texts_at(accepted_commit(), need)
    lines = {}
    say(f'{len(indep)} statements proved more than once; {len(need)} files read')

    def parts(i):
        """(statement text, proof text, column of the declaration) of declaration i, or None."""
        m = modnames[g.mods[i]]
        r = ranges.get((m, g.names[i]))
        if r is None or m not in text:
            return None
        if m not in lines:
            lines[m] = text[m].split('\n')
        s = split_decl(text[m], lines[m], r)
        if s is None:
            return None
        return text[m][s[0]:s[1]], text[m][s[1]:s[2]], r

    edits, stats = [], collections.Counter()
    for tsize, roots in indep:
        ms = sorted(roots, key=lambda i: (topo[g.mods[i]], g.names[i]))
        info = {}
        for i in ms:
            p = parts(i)
            if p is not None:
                info[i] = p + (g.vsize[i] + aux.get((g.mods[i], g.names[i]), 0), CONE.count_tokens(p[1]))
        for d in ms:
            if d not in info:
                continue
            stmt, proof, r, cost, ptok = info[d]
            md = g.mods[d]
            cite = None
            for c in ms:
                if c == d:
                    continue
                mc = g.mods[c]
                if mc != md:
                    if (closure[md] >> bit[mc]) & 1 and not g.names[c].startswith('_private.'):
                        cite = c
                        break
                else:
                    rc = ranges.get((modnames[mc], g.names[c]))
                    if rc is not None and (rc[2], rc[3]) <= (r[0], r[1]):
                        cite = c
                        break
            base = {'module': modnames[md], 'theorem': g.names[d], 'first_line': r[0], 'first_col': r[1],
                    'last_line': r[2], 'last_col': r[3], 'old_written_out': cost, 'old_proof_tokens': ptok}
            if kind == 'citations':
                if cite is None:
                    continue
                cname = CD.user_name(g.names[cite]) if g.names[cite].startswith('_private.') else '_root_.' + g.names[cite]
                if ptok < min_tokens:
                    stats['proof too short to be worth a citation'] += 1
                    continue
                body = LONG.format(c=cname) if form == 'first' else ' @' + cname
                edits.append(dict(base, body=body, tag='cite', source=g.names[cite]))
                stats['citations'] += 1
            else:
                if cite is not None:
                    continue                          # handled by a citation
                # the shortest proof of the same statement, preferring one whose statement is written the same way
                def norm(s):
                    return ' '.join(s.split())
                cands = sorted((info[c][3], info[c][4], c) for c in ms if c != d and c in info
                               and 'where' not in info[c][1] and 'termination_by' not in info[c][1])
                cands = [x for x in cands if cost - x[0] >= 200 and x[1] <= ptok]
                if not cands:
                    stats['no smaller proof that is not longer in source'] += 1
                    continue
                def rest(i):
                    """Statement text after the theorem's own name: binders and the claim."""
                    st = info[i][0]
                    short = CD.user_name(g.names[i]).split('.')[-1]
                    k = st.find(short)
                    return norm(st[k + len(short):]) if k >= 0 else norm(st)
                same = [x for x in cands if rest(x[2]) == rest(d)]
                src = (same or cands)[0][2]
                sproof, sr = info[src][1], info[src][2]
                shift = r[1] - sr[1]
                if shift:
                    parts_ = sproof.split('\n')
                    if shift > 0:
                        sproof = '\n'.join([parts_[0]] + [(' ' * shift + l) if l.strip() else l for l in parts_[1:]])
                    elif all((not l.strip()) or l.startswith(' ' * -shift) for l in parts_[1:]):
                        sproof = '\n'.join([parts_[0]] + [l[-shift:] if l.strip() else l for l in parts_[1:]])
                    else:
                        stats['indentation does not fit'] += 1
                        continue
                edits.append(dict(base, body=sproof, tag='transplant', source=g.names[src],
                                  source_module=modnames[g.mods[src]], same_statement_text=bool(same),
                                  expected_written_out=info[src][3], new_proof_tokens=info[src][4]))
                stats['transplants'] += 1
                stats['  with identically written statement'] += 1 if same else 0
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    with open(out, 'w', encoding='utf-8') as fh:
        for e in edits:
            fh.write(json.dumps(e, ensure_ascii=False) + '\n')
    for k, v in stats.items():
        print(f'  {k}: {v:,}')
    say(f'{len(edits)} edits in {len({e["module"] for e in edits})} files written to {out}')


LONG_RE = re.compile(r':=( by first \| exact @(?P<c>\S+) \| exact (?P=c) \| \(intros; apply (?P=c) <;> assumption\))')


def gen_shorten(out, candidates):
    """Edits that shorten citations already in the accepted state. The long form tries three ways to
    cite; the compiled proof shows which one applied. If the proof is the bare cited theorem, `@C`
    is enough (2 tokens instead of 18); otherwise `by intros; apply C <;> assumption` (7).

    candidates: the table tools/cite_duplicates.py wrote before the citations were made; it names
    the files to look at."""
    t0 = time.time()

    def say(msg):
        print(f'{msg}  [{time.time() - t0:.0f}s]', flush=True)

    overlay_consts = os.path.join(C.DATA_OVERLAY, 'consts.tsv')
    g = CONE.load_graph(C.DATA_BASE, overlay_consts if os.path.exists(overlay_consts) else None, (), say)
    ranges = CD.load_ranges(g.patched)
    by_mod = collections.defaultdict(list)             # module -> [(range, name)]
    for (m, name), r in ranges.items():
        if m in g.patched:
            by_mod[m].append((r, name))
    vsize = {}
    for i in range(g.n):
        if g.modnames[g.mods[i]] in g.patched and g.kinds[i] == 'thm':
            vsize[(g.modnames[g.mods[i]], g.names[i])] = g.vsize[i]
    old_place = {}
    with open(candidates, encoding='utf-8') as fh:
        head = fh.readline().rstrip('\n').split('\t')
        for line in fh:
            r = dict(zip(head, line.rstrip('\n').split('\t')))
            old_place[(r['module'], r['theorem'])] = tuple(int(r[k]) for k in ('first_line', 'first_col', 'last_line', 'last_col'))
    mods = sorted({m for m, _ in old_place} & set(g.patched))
    new_text = texts_at(accepted_commit(), mods)
    old_text = texts_at(C.UPSTREAM_TAG, mods)
    edits, stats = [], collections.Counter()
    for m in mods:
        text = new_text.get(m)
        if text is None or ':= by first | exact @' not in text:
            continue
        lines = text.split('\n')
        spans = []
        for r, name in by_mod[m]:
            spans.append((CD.offset(lines, r[0], r[1]), CD.offset(lines, r[2], r[3]), r, name))
        for mm in LONG_RE.finditer(text):
            owner = [sp for sp in spans if sp[0] <= mm.start() < sp[1]]
            if not owner:
                stats['citation outside any known declaration'] += 1
                continue
            a, b, r, name = min(owner, key=lambda sp: sp[1] - sp[0])
            c = mm.group('c')
            v = vsize.get((m, name))
            body = ' @' + c if v == 1 else f' by intros; apply {c} <;> assumption'
            new_tokens = 2 if v == 1 else 7
            tag = 'shorten:term' if v == 1 else 'shorten:apply'
            # (Where the original proof was shorter still, the citation is kept anyway: putting the proof
            # back would raise the written-out size, and a change may not raise a dial.)
            stats[tag] += 1
            edits.append({'module': m, 'theorem': name, 'first_line': r[0], 'first_col': r[1], 'last_line': r[2],
                          'last_col': r[3], 'body': body, 'tag': tag, 'source': c})
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    with open(out, 'w', encoding='utf-8') as fh:
        for e in edits:
            fh.write(json.dumps(e, ensure_ascii=False) + '\n')
    for k, v in stats.items():
        print(f'  {k}: {v:,}')
    say(f'{len(edits)} edits in {len({e["module"] for e in edits})} files written to {out}')


# ------------------------------------------------------------------ variants
# ------------------------------------------------------------------ projections instead of taking apart
# `obtain ⟨-, -, h, -, …⟩ := H` on a long conjunction is written out as one nested case split per part,
# and every level restates what is left of the conjunction, dropped parts included. Skipping the dropped
# parts by projection (`obtain ⟨h, -⟩ := H.2.2`) leaves only the levels that are used. These edits replace
# one such line each; the proof is otherwise untouched, and each edit has to compile and pass the
# equivalence check.
KW_RE = re.compile(r'^(?P<lead>[ \t]*(?:·[ \t]*)?)(?P<kw>obtain|obt|have|rcases)[ \t]+')
IDENT_RE = re.compile(r"^[^\W\d][\w'!?]*$")
ATOM_RE = re.compile(r'^[^\s()\[\]{}⟨⟩@]+$')
PLAIN_RE = re.compile(r"^[^\W\d][\w']*$")
OPEN, CLOSE = '([{⟨', ')]}⟩'
SPLIT = 6                          # dropped parts in a row, inside a pattern, from which a new line pays
MIN_SAVED = 3                      # levels of case split a rewrite must save for a line to be touched


def split_site(line):
    """`obtain ⟨a, -, ⟨b, c⟩⟩ := t` (also `obt`, `have`, and `rcases t with ⟨…⟩`) -> (text before the
    keyword, keyword, t, the entries of the outer pattern), or None if the line is not of that shape."""
    m = KW_RE.match(line)
    if not m:
        return None
    lead, kw, rest = m.group('lead'), m.group('kw'), line[m.end():].rstrip()
    term = None
    if kw == 'rcases':
        w = rest.rfind(' with ⟨')
        if w < 0:
            return None
        term, rest = rest[:w].strip(), rest[w + len(' with '):]
    if not rest.startswith('⟨'):
        return None
    depth, end = 0, None
    for i, ch in enumerate(rest):
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
            if depth == 0:
                end = i
                break
    if end is None or rest[end] != '⟩':
        return None
    inner, after = rest[1:end], rest[end + 1:].strip()
    if kw == 'rcases':
        if after:
            return None
    else:
        if not after.startswith(':='):
            return None
        term = after[2:].strip()
    if not term:
        return None
    parts, depth, cur = [], 0, ''
    for ch in inner:
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
        if depth == 0 and ch == '|':                      # alternatives: not a plain tuple
            return None
        if depth == 0 and ch == ',':
            parts.append(cur.strip())
            cur = ''
        else:
            cur += ch
    parts.append(cur.strip())
    if depth or not all(parts):
        return None
    return lead, kw, term, parts


def projection_lines(line, next_indent, before, after, fresh, min_parts):
    """The replacement for one tactic line that takes a flat tuple apart, or None if the line is not
    one we can rewrite safely. before/after: the declaration's text before and after the line.

    Dropped parts are not matched one by one. A run of them is skipped by projection (`H.2.2.2`) where a
    term to project from is at hand: at the start of the pattern, or after a long run in the middle, where
    the pattern is ended with a name for what is left and a new line goes on from there. Dropped parts at
    the end of the pattern become one `-`, which matches all that is left. Named parts stay in a pattern,
    so witnesses of an existence statement among them are still handled. The result is never longer in
    tokens than the line it replaces, even counting every projection step as a token."""
    if '--' in line or ';' in line:
        return None
    site = split_site(line)
    if site is None:
        return None
    lead, kw, term, parts = site
    k = len(parts)
    if k < min_parts or next_indent > len(lead):         # too short to matter, or the term continues below
        return None
    # An entry is dropped (`-`, `_`) or kept. A kept entry may be a name or a pattern of its own; it is
    # copied as it stands.
    drop = [p in ('-', '_') for p in parts]
    if not any(drop) or all(drop):
        return None
    depth = 0
    for ch in term:
        depth += (ch in OPEN) - (ch in CLOSE)
        if depth < 0:
            return None
    if depth or term.split()[-1] in ('by', 'fun', '=>', ':=', 'with', 'at', 'from', '<|', '$', 'do'):
        return None
    atom = bool(ATOM_RE.match(term))
    if not atom and term.startswith('('):                # `(f x).1` can be projected from as it stands
        depth = 0
        for j, ch in enumerate(term):
            depth += (ch in OPEN) - (ch in CLOSE)
            if depth == 0:
                atom = bool(re.fullmatch(r"(\.[\w']+)*", term[j + 1:]))
                break
    last_named = max(i for i in range(k) if not drop[i])

    # statements: (term to take apart, pattern entries); the first one keeps the line's keyword
    stmts, gone = [], []
    cur, pat, i = (term if atom else f'({term})'), [], 0
    plain_first = True                                   # the first statement still takes `term` itself apart
    while i < k:
        if not drop[i]:
            pat.append(parts[i])
            i += 1
            continue
        j = i
        while j < k and drop[j]:
            j += 1
        run = j - i
        if i > last_named:                               # nothing named follows: one dash matches the rest
            pat.append('-')
            break
        if not pat:                                      # at the start of a statement: skip by projection
            cur += '.2' * run
            if not stmts:
                plain_first = False
        elif run >= SPLIT:                               # a long run in the middle: go on from a name
            name = fresh()
            stmts.append((cur, pat + [name]))
            gone.insert(0, name)
            cur, pat = name + '.2' * run, []
        else:
            pat += parts[i:j]
        i = j
    if pat:
        stmts.append((cur, pat))

    def left_only(pat):
        """`⟨h, -⟩` with h named like a hypothesis: the left part of a conjunction, read as `.1`."""
        return len(pat) == 2 and pat[1] == '-' and pat[0][:1] in 'hH' and bool(IDENT_RE.match(pat[0]))

    # A pattern of n entries is n - 1 levels of case split; a line that only projects has none.
    levels = sum(0 if len(p) == 1 or left_only(p) else len(p) - 1 for _, p in stmts)
    if (k - 1) - levels < MIN_SAVED:                      # too few levels saved to matter
        return None
    if left_only(stmts[0][1]):
        plain_first = False                              # the first line projects out of the term too

    def write(first, cur, pat):
        if first and plain_first:
            cur = term                                   # the whole term, as in the original line
        if len(pat) == 1:
            return f'have {pat[0]} := {cur}' if IDENT_RE.match(pat[0]) else f'obtain {pat[0]} := {cur}'
        if left_only(pat):
            return f'have {pat[0]} := {cur}.1'
        body = '⟨' + ', '.join(pat) + '⟩'
        if not first:
            return f'obtain {body} := {cur}'
        return f'rcases {cur} with {body}' if kw == 'rcases' else f'{kw} {body} := {cur}'

    out = [write(n == 0, c, p) for n, (c, p) in enumerate(stmts)]
    word = re.compile(r'(?<![\w.\'])' + re.escape(term) + r'(?![\w\'])')
    # `obtain` and `rcases` consume a hypothesis they take apart. Where we now project out of it instead,
    # clear it, so that the context stays what it was.
    if (not plain_first and kw in ('obtain', 'rcases') and PLAIN_RE.match(term) and term not in parts
            and word.search(before) and not word.search(after)):
        gone.append(term)
    if gone:
        out.append('clear ' + ' '.join(gone))
    pad = ' ' * len(lead)
    return lead + ('\n' + pad).join(out)


MIN_REST = 4                       # parts from the first dropped one on, below which gathered_lines leaves a line


def gathered_lines(line, next_indent, before, after, fresh, min_parts):
    """A costlier rewrite for patterns whose dropped parts lie between the kept ones, where skipping by one
    projection is not possible: every kept part after the first dropped one is read by its own projection.
    Names at the front stay in a pattern (they may be witnesses). After that, if all names look like
    hypotheses, the projections are gathered in one term, where they share everything, and named from it;
    otherwise each run of names is taken out by a short `obtain`. This adds source when every projection
    step is counted, so `choose` keeps a file only where the written-out size pays for it."""
    if '--' in line or ';' in line:
        return None
    site = split_site(line)
    if site is None:
        return None
    lead, kw, term, parts = site
    k = len(parts)
    if k < min_parts or next_indent > len(lead):
        return None
    for p in parts:
        if p not in ('-', '_') and (p == 'rfl' or not IDENT_RE.match(p)):
            return None
    front = 0
    while front < k and parts[front] not in ('-', '_'):
        front += 1
    rest = parts[front:]
    r = len(rest)
    names = [(i, p) for i, p in enumerate(rest) if p not in ('-', '_')]
    if r < MIN_REST:
        return None
    depth = 0
    for ch in term:
        depth += (ch in OPEN) - (ch in CLOSE)
        if depth < 0:
            return None
    if depth or term.split()[-1] in ('by', 'fun', '=>', ':=', 'with', 'at', 'from', '<|', '$', 'do'):
        return None

    def proj(i):
        return '.2' * i + ('.1' if i < r - 1 else '')

    out, gone = [], []
    if front:
        base = fresh() if names else '-'
        pat = '⟨' + ', '.join(parts[:front] + [base]) + '⟩'
        out.append(f'rcases {term} with {pat}' if kw == 'rcases' else f'{kw} {pat} := {term}')
        if names:
            gone.append(base)
    else:
        if not names:
            return None
        atom = bool(ATOM_RE.match(term))
        base = term
        word = re.compile(r'(?<![\w.\'])' + re.escape(term) + r'(?![\w\'])')
        if (kw in ('obtain', 'rcases') and PLAIN_RE.match(term) and term not in [n for _, n in names]
                and word.search(before) and not word.search(after)):
            gone.append(term)
        if not atom:
            if len(names) == 1:
                base = f'({term})'
            else:
                base = fresh()
                out.append(f'have {base} := {term}')
                gone.insert(0, base)
    if names and not all(n[:1] in 'hH' for _, n in names):
        cur, i = base, 0
        while True:
            d = 0
            while i < r and rest[i] in ('-', '_'):
                i, d = i + 1, d + 1
            if i == r:
                break
            j = i
            while j < r and rest[j] not in ('-', '_'):
                j += 1
            run, tail = rest[i:j], cur + '.2' * d
            if j == r:
                out.append(f'have {run[0]} := {tail}' if len(run) == 1 else f'obtain ⟨{", ".join(run)}⟩ := {tail}')
                break
            if all(p in ('-', '_') for p in rest[j:]):
                out.append(f'have {run[0]} := {tail}.1' if len(run) == 1 and run[0][:1] in 'hH'
                           else f'obtain ⟨{", ".join(run)}, -⟩ := {tail}')
                break
            nxt = fresh()
            out.append(f'obtain ⟨{", ".join(run)}, {nxt}⟩ := {tail}')
            gone.insert(0, nxt)
            cur, i = nxt, j
    elif len(names) == 1:
        (i, n), = names
        out.append(f'have {n} := {base}{proj(i)}')
    elif names:
        items = [base + proj(i) for i, _ in names]
        gathered = items[-1]
        for it in reversed(items[:-1]):
            gathered = f'And.intro {it} ({gathered})' if ' ' in gathered else f'And.intro {it} {gathered}'
        both = fresh()
        out.append(f'have {both} := {gathered}')
        last = len(names) - 1
        out += [f'have {n} := {both}' + '.2' * j + ('.1' if j < last else '') for j, (_, n) in enumerate(names)]
        gone.insert(0, both)
    if gone:
        out.append('clear ' + ' '.join(gone))
    new = lead + ('\n' + ' ' * len(lead)).join(out)
    return None if new == line else new


# `set x := e with h` leaves x transparent: `ring`, `linarith` and their relatives see through it and
# multiply out whatever powers and products e contains. With `clear_value x` right after, x is a plain
# variable and `h : x = e` is still there for the steps that need the value.
SET_RE = re.compile(r'^(?P<lead>[ \t]*(?:·[ \t]*)?)set[ \t]+(?P<x>[^\s:(){}\[\]⟨⟩]+)[ \t]*(?::[^=\n]*)?:=[^\n]*'
                    r'\bwith[ \t]+(?:←[ \t]*)?[^\s]+[ \t]*$')
ARITH_RE = re.compile(r'\b(ring|ring_nf|linarith|nlinarith|field_simp|positivity|polyrith|linear_combination)\b')


def opaque_set_lines(line, next_indent, before, after, fresh, min_parts):
    if '--' in line or ';' in line:
        return None
    m = SET_RE.match(line)
    if not m or next_indent > len(m.group('lead')) or not IDENT_RE.match(m.group('x')):
        return None
    if not ARITH_RE.search(after):
        return None
    return line + '\n' + ' ' * len(m.group('lead')) + 'clear_value ' + m.group('x')


REWRITES = {    # tag -> (how a line must start, the rewrite)
    'projections': (('obtain ⟨', 'obt ⟨', 'have ⟨', 'rcases '), projection_lines),
    'projections-gathered': (('obtain ⟨', 'obt ⟨', 'have ⟨', 'rcases '), gathered_lines),
    'opaque-set': (('set ',), opaque_set_lines),
}


def gen_projections(out, min_parts, min_nodes, tag='projections', skip=()):
    """Edits of single lines in cone theorems whose proof is written out in at least `min_nodes` nodes.
    `projections`: `obtain ⟨…⟩ := H` (also `obt`, `rcases H with ⟨…⟩`, `have ⟨…⟩ := H`) with a flat
    pattern of at least `min_parts` parts is replaced by projections. `opaque-set`: `clear_value x` is
    added after `set x := e with h` where an arithmetic tactic follows."""
    starts_with, rewrite = REWRITES[tag]
    t0 = time.time()

    def say(msg):
        print(f'{msg}  [{time.time() - t0:.0f}s]', flush=True)

    overlay_consts = os.path.join(C.DATA_OVERLAY, 'consts.tsv')
    g = CONE.load_graph(C.DATA_BASE, overlay_consts if os.path.exists(overlay_consts) else None, (), say)
    by_name = CONE.find_names(g, set(C.TARGETS))
    cone = CONE.reach(g, [by_name[t] for t in C.TARGETS])
    ranges = CD.load_ranges(g.patched)
    aux = collections.Counter()
    for i in range(g.n):
        if cone[i] and IFACE.AUX.search(g.names[i]):
            nm = g.names[i]
            aux[(g.mods[i], nm[:IFACE.AUX.search(nm).start()])] += g.tsize[i] + g.vsize[i]
    cands = collections.defaultdict(list)                 # module -> [(range, name, proof size)]
    for i in range(g.n):
        if not cone[i] or g.kinds[i] != 'thm' or IFACE.AUX.search(g.names[i]):
            continue
        size = g.vsize[i] + aux[(g.mods[i], g.names[i])]
        m = g.modnames[g.mods[i]]
        if size >= min_nodes and m not in skip and (m, g.names[i]) in ranges:
            cands[m].append((ranges[(m, g.names[i])], g.names[i], size))
    say(f'{sum(len(v) for v in cands.values()):,} cone theorems of at least {min_nodes:,} nodes in {len(cands):,} files')
    mods = sorted(cands)
    edits, stats = [], collections.Counter()
    for lo in range(0, len(mods), 2000):
        text = texts_at(accepted_commit(), mods[lo:lo + 2000])
        for m in mods[lo:lo + 2000]:
            src = text.get(m)
            if src is None:
                continue
            lines = src.split('\n')
            starts = [0]
            for l in lines:
                starts.append(starts[-1] + len(l) + 1)
            n_fresh = [0]

            def fresh():
                while True:
                    name = f'hz{n_fresh[0]}'
                    n_fresh[0] += 1
                    if name not in src:
                        return name

            for r, name, size in cands[m]:
                s = split_decl(src, lines, r)
                if s is None:
                    stats['declarations whose statement end was not found'] += 1
                    continue
                a, body_start, b = s
                first = src.count('\n', 0, body_start)
                last = src.count('\n', 0, b)
                for ln in range(first, last + 1):
                    line = lines[ln]
                    st = line.lstrip(' \t·')
                    if (not st.startswith(starts_with) or starts[ln] < body_start
                            or starts[ln] + len(line) > b):
                        continue
                    nxt = next((l for l in lines[ln + 1:last + 1] if l.strip()), '')
                    next_indent = len(nxt) - len(nxt.lstrip(' \t')) if ln + 1 <= last and nxt else 0
                    new = rewrite(line, next_indent, src[a:starts[ln]], src[starts[ln + 1]:b], fresh, min_parts)
                    if new is None:
                        continue
                    stats['sites'] += 1
                    edits.append({'module': m, 'theorem': name, 'first_line': ln, 'first_col': 0,
                                  'start': starts[ln], 'end': starts[ln] + len(line),
                                  'old_sha': hashlib.sha256(line.encode('utf-8')).hexdigest(),
                                  'body': new, 'tag': tag, 'size': size})
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    with open(out, 'w', encoding='utf-8') as fh:
        for e in edits:
            fh.write(json.dumps(e, ensure_ascii=False) + '\n')
    for k, v in stats.items():
        print(f'  {k}: {v:,}')
    theorems = {(e['module'], e['theorem']): e['size'] for e in edits}
    say(f'{len(edits)} edits in {len(theorems):,} theorems ({sum(theorems.values()):,} nodes) in '
        f'{len({e["module"] for e in edits}):,} files written to {out}')


def load_edits(path):
    per = collections.defaultdict(list)
    with open(path, encoding='utf-8') as fh:
        for line in fh:
            e = json.loads(line)
            per[e['module']].append(e)
    for m in per:
        per[m].sort(key=lambda e: (e['first_line'], e['first_col']))
    return per


def write_variant(work, vid, module, text):
    p = C.module_path(module, os.path.join(work, 'v', vid))
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, 'w', encoding='utf-8', newline='') as fh:
        fh.write(text)


def load_results(path):
    res = {}
    if os.path.exists(path):
        with open(path) as fh:
            for line in fh:
                try:
                    r = json.loads(line)
                    res[(r['variant'], r['module'])] = r
                except ValueError:
                    pass
    return res


def good(r):
    return bool(r and r.get('ok') and r.get('compatible') and not r.get('added') and not r.get('sorry'))


def variants(edits_path, work, single_from, modules_file=None):
    per = load_edits(edits_path)
    if modules_file:
        with open(modules_file) as fh:
            want = {l.strip() for l in fh if l.strip()}
        per = {m: es for m, es in per.items() if m in want}
    res = load_results(single_from) if single_from else {}
    text = texts_at(accepted_commit(), sorted(per))
    plan = []
    n_unplaced = 0
    for m, es in sorted(per.items()):
        if m not in text:
            continue
        if not single_from:
            new, failed = apply_edits(text[m], es)
            if failed:
                # The file is not the one the edits were made for (this machine's accepted state is behind,
                # or ahead). A variant with only some edits could never match the source elsewhere: skip.
                n_unplaced += 1
                continue
            write_variant(work, 'all', m, new)
            plan.append(('all', m))
            continue
        if good(res.get(('all', m))) or ('all', m) not in res:
            continue
        singles = [k for k in range(len(es)) if good(res.get((f'e{k}', m)))]
        tried = [k for k in range(len(es)) if (f'e{k}', m) in res]
        if not tried and len(es) > 1:
            for k, e in enumerate(es):
                new, failed = apply_edits(text[m], [e])
                if not failed:
                    write_variant(work, f'e{k}', m, new)
                    plan.append((f'e{k}', m))
        elif len(singles) > 1 and ('combine', m) not in res:
            new, failed = apply_edits(text[m], [es[k] for k in singles])
            write_variant(work, 'combine', m, new)
            plan.append(('combine', m))
    name = 'plan_single.tsv' if single_from else 'plan_all.tsv'
    with open(os.path.join(work, name), 'w') as fh:
        for vid, m in plan:
            fh.write(f'{vid}\t{m}\n')
    print(f'{len(plan)} variants written under {os.path.join(work, "v")}; plan: {os.path.join(work, name)}'
          + (f'; {n_unplaced} files skipped: they differ from the files the edits were made for' if n_unplaced else ''))


EXCHANGE = 1000                    # nodes of written-out size that one added source token must buy (the judge's rate)


def strict_tokens(text):
    """Source tokens with every numeric projection step counted. The dial counts a dotted name as one
    token whatever its length, so `h.2.2.1` is one token there and four here. Edits that turn patterns
    into projection chains are held to this stricter count, so that they do not lean on that convention."""
    n = 0
    for t in CONE.TOKEN.findall(CONE.strip_comments(text)):
        n += 1
        if '.' in t and t[0] not in '"0123456789':
            n += sum(1 for part in t.split('.')[1:] if part.isdigit())
    return n


def choose(edits_path, work):
    per = load_edits(edits_path)
    res = load_results(os.path.join(work, 'results.jsonl'))
    final = os.path.join(work, 'final', 'new')
    shutil.rmtree(os.path.join(work, 'final'), ignore_errors=True)
    os.makedirs(final)
    chosen, stats = [], collections.Counter()
    times = {}
    sources = []                                          # (module, variant, sha256 of the source that was compiled)
    accepted = texts_at(accepted_commit(), sorted(per))
    for m, es in sorted(per.items()):
        options = []                                      # (written-out of the module, variant, edits)
        r = res.get(('all', m))
        if good(r):
            options.append((r['written_out'], 'all', es))
        r = res.get(('combine', m))
        if good(r):
            options.append((r['written_out'], 'combine', [es[k] for k in range(len(es)) if good(res.get((f'e{k}', m)))]))
        for k in range(len(es)):
            r = res.get((f'e{k}', m))
            if good(r):
                options.append((r['written_out'], f'e{k}', [es[k]]))
        tried = any((v, m) in res for v in ['all', 'combine'] + [f'e{k}' for k in range(len(es))])
        if not options:
            stats['files with no passing variant' if tried else 'files not compiled'] += 1
            continue
        # Each file stands on its own: its written-out size must fall, and if its source grows (counting
        # every projection step) the fall must be at least EXCHANGE nodes per token added.
        before = strict_tokens(accepted[m]) if m in accepted else None
        paying = []
        for w, vid, used in options:
            old = res[(vid, m)].get('old_written_out')
            if old is None or before is None or w >= old:
                continue
            with open(C.module_path(m, os.path.join(work, 'v', vid)), encoding='utf-8') as fh:
                added = strict_tokens(fh.read()) - before
            if added <= 0 or old - w >= EXCHANGE * added:
                paying.append((w, vid, used, added))
        if not paying:
            stats['files where nothing got smaller, or the gain does not pay for the added source'] += 1
            continue
        w, vid, used, added = min(paying, key=lambda o: o[0])
        r = res[(vid, m)]
        stats['files kept'] += 1
        stats['edits kept'] += len(used)
        stats['written-out before'] += r.get('old_written_out') or 0
        stats['written-out after'] += w
        stats['source tokens added, counting every projection step'] += added
        with open(C.module_path(m, os.path.join(work, 'v', vid)), 'rb') as fh:
            sources.append((m, vid, hashlib.sha256(fh.read()).hexdigest()))
        for e in used:
            chosen.append(e)
        for ext in ('.olean', '.ilean'):
            src = C.module_path(m, os.path.join(work, 'out', vid), ext)
            dst = C.module_path(m, final, ext)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copyfile(src, dst)
        if r.get('time_s') is not None and r.get('old_time_s') is not None:
            times[m] = {'before': r['old_time_s'], 'after': r['time_s']}
    with open(os.path.join(work, 'chosen.jsonl'), 'w', encoding='utf-8') as fh:
        for e in chosen:
            fh.write(json.dumps(e, ensure_ascii=False) + '\n')
    with open(os.path.join(work, 'final', 'modules.txt'), 'w') as fh:
        fh.write('\n'.join(sorted({e['module'] for e in chosen})) + '\n')
    json.dump(times, open(os.path.join(work, 'final', 'times.json'), 'w'))
    with open(os.path.join(work, 'final', 'sources.tsv'), 'w') as fh:
        for m, vid, digest in sources:
            fh.write(f'{m}\t{vid}\t{digest}\n')
    for k, v in stats.items():
        print(f'  {k}: {v:,}')
    print(f'chosen edits: {os.path.join(work, "chosen.jsonl")}; compiled files: {final}')


def apply(chosen_path, src=C.SRC, expect=None, drop_stale=False):
    """Write the chosen edits into the source tree. With `expect` (W/final/sources.tsv from `choose`),
    refuse unless every file written is byte-identical to the source that was compiled. With
    `drop_stale`, files that would not be identical (they have changed here since the other machine
    was brought up to date) are left untouched instead, and the files written are listed in
    applied_modules.txt next to the chosen edits, for the judge's --only-file."""
    per = load_edits(chosen_path)
    want = {}
    if expect:
        with open(expect) as fh:
            for line in fh:
                m, _vid, digest = line.rstrip('\n').split('\t')
                want[m] = digest
        if set(want) != set(per):
            sys.exit(f'{expect} lists {len(want)} files, the chosen edits cover {len(per)}: they do not belong together')
    text = texts_at(accepted_commit(), sorted(per))
    out, stale = {}, []
    for m, es in sorted(per.items()):
        new, failed = apply_edits(text[m], es)
        if failed or (expect and hashlib.sha256(new.encode('utf-8')).hexdigest() != want[m]):
            stale.append(m)
        else:
            out[m] = new
    if stale and not drop_stale:
        sys.exit(f'{len(stale)} file(s) would differ from the source that was compiled, nothing written; first: {stale[0]}'
                 if expect else f'{stale[0]}: edit(s) could not be placed; is the accepted state the one they were made for?')
    for m, new in out.items():
        with open(C.module_path(m, src), 'w', encoding='utf-8', newline='') as fh:
            fh.write(new)
    with open(os.path.join(os.path.dirname(os.path.abspath(chosen_path)), 'applied_modules.txt'), 'w') as fh:
        fh.write('\n'.join(sorted(out)) + '\n')
    print(f'applied {sum(len(per[m]) for m in out)} edits in {len(out)} files'
          + ('; every file written equals the source that was compiled' if expect else '')
          + (f'; {len(stale)} files left alone because they have changed here since' if stale else ''))


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    for name in ('citations', 'transplants'):
        s = sub.add_parser(name)
        s.add_argument('--out', required=True)
        s.add_argument('--form', choices=['first', 'short'], default='first')
        s.add_argument('--min-proof-tokens', type=int, default=LONG_TOKENS + 1)
    sh = sub.add_parser('shorten')
    sh.add_argument('--out', required=True)
    sh.add_argument('--candidates', default=os.path.join(C.ROOT, 'build', 'cite', 'candidates.tsv'))
    for name in REWRITES:
        pj = sub.add_parser(name)
        pj.add_argument('--out', required=True)
        pj.add_argument('--min-parts', type=int, default=5)
        pj.add_argument('--min-nodes', type=int, default=20000)
        pj.add_argument('--min-saved', type=int, default=MIN_SAVED, help='levels of case split a rewrite must save')
        pj.add_argument('--skip', default=None, help='file naming modules to leave out, one per line')
    v = sub.add_parser('variants')
    v.add_argument('--edits', required=True); v.add_argument('--work', required=True)
    v.add_argument('--single-from', default=None); v.add_argument('--modules', default=None)
    c = sub.add_parser('choose')
    c.add_argument('--edits', required=True); c.add_argument('--work', required=True)
    a = sub.add_parser('apply')
    a.add_argument('--chosen', required=True)
    a.add_argument('--expect', default=None, help='W/final/sources.tsv: refuse unless the files come out byte-identical')
    a.add_argument('--drop-stale', action='store_true', help='leave out files that would not come out identical')
    args = ap.parse_args()
    if args.cmd in ('citations', 'transplants'):
        gen(args.cmd, args.out, args.form, args.min_proof_tokens)
    elif args.cmd == 'shorten':
        gen_shorten(args.out, args.candidates)
    elif args.cmd in REWRITES:
        globals()['MIN_SAVED'] = args.min_saved
        skip = set()
        if args.skip:
            with open(args.skip) as fh:
                skip = {l.strip() for l in fh if l.strip()}
        gen_projections(args.out, args.min_parts, args.min_nodes, args.cmd, skip)
    elif args.cmd == 'variants':
        os.makedirs(args.work, exist_ok=True)
        variants(args.edits, args.work, args.single_from, args.modules)
    elif args.cmd == 'choose':
        choose(args.edits, args.work)
    else:
        apply(args.chosen, expect=args.expect, drop_stale=args.drop_stale)


if __name__ == '__main__':
    main()
