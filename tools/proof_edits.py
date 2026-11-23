#!/usr/bin/env python3
"""Replace the proofs of chosen theorems, trying alternatives side by side and keeping what passes.

An edit is: in this module, replace everything after the `:=` that ends this theorem's statement by
this text. The statement itself is never touched. Edits are generated from the tables (a citation
of a copy the file already imports, or the text of the shortest proof of the same statement found
elsewhere), so they are guesses: each one has to compile and pass the equivalence check.

  tools/proof_edits.py citations  --out build/x/edits.jsonl [--form first|short] [--min-proof-tokens N]
  tools/proof_edits.py transplants --out build/x/edits.jsonl
  tools/proof_edits.py import-citations --out build/x/edits.jsonl   # cite a copy through one added import;
                                                               # run variants and choose with --allow-imports
  tools/proof_edits.py shorten     --out build/x/edits.jsonl    # shorten citations already recorded
  tools/proof_edits.py projections --out build/x/edits.jsonl [--min-parts N] [--min-nodes N]
                                                               # read long conjunctions by projection
  tools/proof_edits.py opaque-set  --out build/x/edits.jsonl [--min-nodes N]
                                                               # `clear_value x` after `set x := e with h`
  tools/proof_edits.py drop-restate --out build/x/edits.jsonl [--min-nodes N]
                                                               # delete `show T` / `change T` / bare `dsimp only`
  tools/proof_edits.py repoint     --out build/x/edits.jsonl [--max-files N]
  tools/proof_edits.py recite      --out build/x/edits.jsonl [--max-files N] [--skip-edits E ...]
                                                               # the same for any two theorems with one
                                                               # statement, when the users can see the other
                                                               # users of a restatement cite the original;
                                                               # choose with --keep-equal
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
import argparse, bisect, collections, hashlib, json, os, re, shutil, subprocess, sys, time

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
    # An edit may need one more import (a citation of a copy in a file this one does not import yet).
    # The import lines go after the file's last import line; a module is never listed twice.
    gone = {id(e) for e in failed}
    need = []
    for e in edits:
        if id(e) not in gone:
            for m in e.get('imports', ()):
                if m not in need:
                    need.append(m)
    if need:
        have = set(IMPORT_LINE.findall(text))
        new = ''.join(f'import {m}\n' for m in need if m not in have)
        if new:
            pos = 0
            for mm in IMPORT_LINE.finditer(text):
                pos = mm.end()
            text = text[:pos] + new + text[pos:]
    return text, failed


IMPORT_LINE = re.compile(r'^import[ \t]+(\S+)[ \t]*\n', re.M)


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


def gen_import_citations(out, min_tokens):
    """Citations that need one added import. A theorem whose file cannot see any other proof of its
    statement cites the earliest public copy, and its file imports the copy's file, when

      (a) the theorem's file already imports everything the copy's file imports, so that the files which
          use it get to see exactly one more module, and
      (b) that module registers nothing that can act on other files (iface.plain_module).

    Added imports always point from a file to one that comes earlier in the order of the import graph,
    so they cannot close a cycle. Needs a few gigabytes of memory for the import closures: run it where
    there is room."""
    import nscheck as NS
    t0 = time.time()

    def say(msg):
        print(f'{msg}  [{time.time() - t0:.0f}s]', flush=True)

    g, ranges, indep, aux = groups_of_copies(say)
    modnames = g.modnames
    midx = {m: k for k, m in enumerate(modnames)}
    imports = [[midx[x] for x in imps if x in midx] for imps in g.mod_imports]
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
    closure = [0] * len(modnames)                         # everything a module imports, directly or not
    outside = [None] * len(modnames)                      # and what it imports from outside the archive
    shared = {}
    for m in order:
        c = 0
        out_names = {x for x in g.mod_imports[m] if x not in midx}
        for i in imports[m]:
            c |= closure[i] | (1 << i)
            out_names |= outside[i]
        closure[m] = c
        key = frozenset(out_names)
        outside[m] = shared.setdefault(key, key)
    say(f'import closures for {len(modnames):,} modules')
    entries = NS.load_entries()
    plain = [m in entries and IFACE.plain_module(entries[m]) for m in modnames]
    need = sorted({modnames[g.mods[i]] for _, roots in indep for i in roots})
    text = texts_at(accepted_commit(), need)
    lines = {}
    edits, stats = [], collections.Counter()
    for tsize, roots in indep:
        ms = sorted(roots, key=lambda i: (topo[g.mods[i]], g.names[i]))
        for d in ms:
            md = g.mods[d]
            seen = closure[md]
            if any(g.mods[c] == md or (seen >> g.mods[c]) & 1 for c in ms if c != d):
                continue                                  # sees a copy already: the plain citation sweep's case
            earlier = [c for c in ms if topo[g.mods[c]] < topo[md]]
            if not earlier:
                stats['earliest copies (they stay)'] += 1
                continue
            cite, why = None, 'every earlier copy is private'
            for c in earlier:
                if g.names[c].startswith('_private.'):
                    continue
                mc = g.mods[c]
                if not plain[mc]:
                    why = 'the copy\'s file registers something that can act on other files'
                elif (any(not ((seen >> i) & 1) for i in imports[mc])
                      or any(not IFACE.outside_import_covered(x, outside[md]) for x in g.mod_imports[mc] if x not in midx)):
                    why = 'the copy\'s file imports something this file does not'
                else:
                    cite = c
                    break
            if cite is None:
                stats['cannot: ' + why] += 1
                continue
            m = modnames[md]
            r = ranges.get((m, g.names[d]))
            if r is None or m not in text:
                continue
            if m not in lines:
                lines[m] = text[m].split('\n')
            s = split_decl(text[m], lines[m], r)
            if s is None:
                continue
            ptok = CONE.count_tokens(text[m][s[1]:s[2]])
            if ptok < min_tokens:
                stats['proof too short to be worth a citation'] += 1
                continue
            edits.append({'module': m, 'theorem': g.names[d], 'first_line': r[0], 'first_col': r[1],
                          'last_line': r[2], 'last_col': r[3],
                          'old_written_out': g.vsize[d] + aux.get((md, g.names[d]), 0), 'old_proof_tokens': ptok,
                          'body': LONG.format(c='_root_.' + g.names[cite]), 'tag': 'cite-import',
                          'source': g.names[cite], 'imports': [modnames[g.mods[cite]]]})
            stats['citations through one added import'] += 1
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    with open(out, 'w', encoding='utf-8') as fh:
        for e in edits:
            fh.write(json.dumps(e, ensure_ascii=False) + '\n')
    for k, v in stats.items():
        print(f'  {k}: {v:,}')
    say(f'{len(edits)} edits in {len({e["module"] for e in edits})} files, '
        f'{sum(e["old_written_out"] for e in edits):,} nodes in the proofs replaced, '
        f'{len({e["imports"][0] for e in edits})} files newly imported; written to {out}')


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


# `show T` and `change T` restate the goal (or a hypothesis) in a form that is equal by computation. Often the
# steps that follow would have worked without it; then the line is only extra source, and the restated
# goal is written out once more in the proof. `dsimp only` with no lemmas is the same kind of step. The
# edit deletes the line; it is kept only if the file still compiles to the same thing.
RESTATE_RE = re.compile(r'^[ \t]*(?:show|change)[ \t]+\S[^\n]*$|^[ \t]*dsimp only(?:[ \t]+at[ \t]+[^\[\n]*)?[ \t]*$')
OPEN_END = ('by', 'fun', '=>', ':=', 'with', 'at', 'from', '<|', '$', 'do', 'then', 'else', '∧', '∨', '→', '↔',
            '=', '≤', '<', '+', '-', '*', '/', ',', '∘', '|>.', '|>', '▸')


def restate_lines(line, next_indent, before, after, fresh, min_parts):
    """'' (delete the line) for a tactic line that only restates the goal, or None to leave it alone."""
    if '--' in line or ';' in line or '·' in line or not RESTATE_RE.match(line):
        return None
    indent = len(line) - len(line.lstrip(' \t'))
    if next_indent > indent:                              # the term continues on the next line
        return None
    words = line.split()
    if words[-1] in OPEN_END or ' from ' in line or ' by ' in line:
        return None
    depth = 0
    for ch in line:
        depth += (ch in OPEN) - (ch in CLOSE)
        if depth < 0:
            return None
    if depth:
        return None
    return ''


# `dsimp only at h` does not look inside instance arguments. After a structure with instance fields has
# been taken apart, hypotheses keep the whole structure literal there, and every substitution after that
# restates it. `dsimp +instances only` reduces those arguments too. (Found by hand in wave 7, where it
# halved two proofs.) The edit is kept only where the file still compiles to the same statements and gets
# smaller.
DSIMP_RE = re.compile(r'^(?P<lead>[ \t]*)dsimp only(?P<rest>(?:[ \t]+\[[^\]\n]*\])?[ \t]+at[ \t]+[^\n]*)$')


def dsimp_instances_lines(line, next_indent, before, after, fresh, min_parts):
    if '--' in line or ';' in line:
        return None
    m = DSIMP_RE.match(line)
    if not m:
        return None
    return m.group('lead') + 'dsimp +instances only' + m.group('rest')


REWRITES = {    # tag -> (how a line must start, the rewrite)
    'projections': (('obtain ⟨', 'obt ⟨', 'have ⟨', 'rcases '), projection_lines),
    'projections-gathered': (('obtain ⟨', 'obt ⟨', 'have ⟨', 'rcases '), gathered_lines),
    'opaque-set': (('set ',), opaque_set_lines),
    'drop-restate': (('show ', 'change ', 'dsimp only'), restate_lines),
    'dsimp-instances': (('dsimp only',), dsimp_instances_lines),
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
                    old = line
                    if new == '' and ln + 1 < len(lines):
                        old = line + '\n'                 # a deleted line goes with its line break
                    edits.append({'module': m, 'theorem': name, 'first_line': ln, 'first_col': 0,
                                  'start': starts[ln], 'end': starts[ln] + len(old),
                                  'old_sha': hashlib.sha256(old.encode('utf-8')).hexdigest(),
                                  'body': new, 'tag': tag, 'size': size, 'tokens': CONE.count_tokens(line)})
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    with open(out, 'w', encoding='utf-8') as fh:
        for e in edits:
            fh.write(json.dumps(e, ensure_ascii=False) + '\n')
    for k, v in stats.items():
        print(f'  {k}: {v:,}')
    theorems = {(e['module'], e['theorem']): e['size'] for e in edits}
    say(f'{len(edits)} edits in {len(theorems):,} theorems ({sum(theorems.values()):,} nodes) in '
        f'{len({e["module"] for e in edits}):,} files written to {out}')


# A local step whose result nothing uses. The demand analysis (tools/demand.py) finds them in the compiled
# proof: `have h : P := proof` where no later step mentions `h`, also not through a tactic that searches the
# context. It gives the names; here the statements that introduce those names are found in the source and
# deleted, one edit each. An edit is kept only if the file still compiles to the same statements and gets
# smaller, so a name that is in fact needed (or was found in the wrong place) costs nothing.
STEP_RE = re.compile(r"^(?P<lead>[ \t]*)(?:have|haveI|let|letI|set)[ \t]+(?P<name>[^\s:(\[{⟨]+)")
ANON_RE = re.compile(r"^(?P<lead>[ \t]*)(?:have|haveI)[ \t]*:")


def gen_unused_steps(out, table, max_modules):
    """Edits that delete local steps whose result is not used. `table`: lines `module, declaration, nodes,
    names` as written by the demand report; the modules with most unused nodes are taken first."""
    t0 = time.time()

    def say(msg):
        print(f'{msg}  [{time.time() - t0:.0f}s]', flush=True)

    want = collections.defaultdict(dict)                  # module -> declaration -> (nodes, names)
    weight = collections.Counter()
    with open(table, encoding='utf-8') as fh:
        for line in fh:
            f = line.rstrip('\n').split('\t')
            if len(f) < 4:
                continue
            want[f[0]][f[1]] = (int(f[2]), set(f[3].split(' ')))
            weight[f[0]] += int(f[2])
    mods = [m for m, _ in weight.most_common(max_modules)]
    say(f'{len(weight):,} modules in the table; taking the {len(mods):,} with most ({sum(weight[m] for m in mods):,} nodes)')
    overlay_consts = os.path.join(C.DATA_OVERLAY, 'consts.tsv')
    g = CONE.load_graph(C.DATA_BASE, overlay_consts if os.path.exists(overlay_consts) else None, (), say)
    ranges = CD.load_ranges(g.patched)
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
            for decl, (nodes, names) in want[m].items():
                r = ranges.get((m, decl))
                if r is None:
                    stats['declarations without a source range'] += 1
                    continue
                sp = split_decl(src, lines, r)
                if sp is None:
                    stats['declarations whose statement end was not found'] += 1
                    continue
                a, body_start, b = sp
                first = src.count('\n', 0, body_start)
                last = src.count('\n', 0, b)
                for ln in range(first + 1, last + 1):
                    line = lines[ln]
                    if starts[ln] < body_start or ';' in line or '--' in line:
                        continue
                    mm = STEP_RE.match(line)
                    if mm and mm.group('name') in names:
                        pass
                    elif 'this' in names and ANON_RE.match(line):
                        mm = ANON_RE.match(line)
                    else:
                        continue
                    indent = len(mm.group('lead'))
                    end = ln + 1                              # the statement: this line and what is indented under it
                    while end <= last and (not lines[end].strip() or len(lines[end]) - len(lines[end].lstrip(' \t')) > indent):
                        end += 1
                    while end > ln + 1 and not lines[end - 1].strip():
                        end -= 1
                    nxt = next((l for l in lines[end:last + 1] if l.strip()), None)
                    if nxt is None or len(nxt) - len(nxt.lstrip(' \t')) != indent or nxt.lstrip().startswith(('·', '|', ')', ']', '}', '⟩')):
                        stats['steps that are the last of their block, or not followed by a step at the same depth'] += 1
                        continue
                    old = src[starts[ln]:starts[end]]
                    if starts[end] > b:
                        continue
                    stats['steps'] += 1
                    edits.append({'module': m, 'theorem': decl, 'first_line': ln, 'first_col': 0,
                                  'start': starts[ln], 'end': starts[end],
                                  'old_sha': hashlib.sha256(old.encode('utf-8')).hexdigest(),
                                  'body': '', 'tag': 'unused-step', 'size': nodes, 'tokens': CONE.count_tokens(old)})
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    with open(out, 'w', encoding='utf-8') as fh:
        for e in edits:
            fh.write(json.dumps(e, ensure_ascii=False) + '\n')
    for k, v in stats.items():
        print(f'  {k}: {v:,}')
    say(f'{len(edits):,} edits in {len({e["module"] for e in edits}):,} files, {sum(e["tokens"] for e in edits):,} tokens in the '
        f'statements to delete; written to {out}')


def comment_spans(text):
    """Sorted (start, end) of the comments of a Lean source: `--` to the end of the line, and nested
    `/- -/` blocks (doc comments included). String literals are skipped."""
    out = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            i += 1
        elif c == '-' and text.startswith('--', i):
            j = text.find('\n', i)
            j = n if j < 0 else j
            out.append((i, j))
            i = j
        elif c == '/' and text.startswith('/-', i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith('/-', j):
                    depth += 1; j += 2
                elif text.startswith('-/', j):
                    depth -= 1; j += 2
                else:
                    j += 1
            out.append((i, j))
            i = j
        else:
            i += 1
    return out


def name_char(c):
    return c.isalnum() or c in "_'!?"


def mentions(src, lo, hi, name, comments):
    """Spans in src[lo:hi], outside comments, where the declaration `name` is mentioned by its name: the
    whole dotted token is the name or ends it (`T.foo` for `A.T.foo`), with `_root_.` in front or not."""
    last = name.rsplit('.', 1)[-1]
    out = []
    i = src.find(last, lo, hi)
    while i >= 0:
        j = i + len(last)
        nxt = i + 1
        if (j >= len(src) or not name_char(src[j])) and (i == 0 or not name_char(src[i - 1])):
            k = i
            while k > 0 and (name_char(src[k - 1]) or src[k - 1] == '.'):
                k -= 1
            tok = src[k:j]
            plain = tok[7:] if tok.startswith('_root_.') else tok
            if plain and plain[0] != '.' and (plain == name or name.endswith('.' + plain)):
                lo_c = bisect.bisect_right(comments, (k, len(src) + 1)) - 1
                if not (lo_c >= 0 and comments[lo_c][0] <= k < comments[lo_c][1]):
                    out.append((k, j))
            nxt = j
        i = src.find(last, nxt, hi)
    return out


RESTATE_SKIP = re.compile(r"(\._proof_\d|\._simp_\d|\.eq_\d+$|\.eq_def$|\._abel_\d|\._ring_\d|\.match_\d|\._auxLemma|\.congr_simp$)")


def gen_repoint(out, max_files):
    """Edits that make the users of a restatement cite the theorem it restates.

    A restatement is a theorem whose statement is, term for term, the statement of another theorem and
    whose proof mentions that theorem and nothing else of the tree. Once every proof the five theorems
    need cites the original, the restatement is no longer needed by them. Only the users' files are
    edited (one name is replaced by another, so a file's own sizes do not change: run `choose` with
    --keep-equal); the restatement stays where it is.

    A restatement is taken only if the five theorems use it in proofs alone (a use inside a statement
    or a definition would change that declaration), and only if every proof that uses it mentions it by
    name in its own source (the dotted name, or an ending of it). Whether a mention found this way is
    the right one is settled by compiling: the file must compile with every statement unchanged.
    Restatements are taken in the order of nodes saved per file to recompile, up to `max_files` files."""
    t0 = time.time()

    def say(msg):
        print(f'{msg}  [{time.time() - t0:.0f}s]', flush=True)

    overlay_consts = os.path.join(C.DATA_OVERLAY, 'consts.tsv')
    g = CONE.load_graph(C.DATA_BASE, overlay_consts if os.path.exists(overlay_consts) else None, (), say)
    by = CONE.find_names(g, set(C.TARGETS))
    cone = CONE.reach(g, [by[t] for t in C.TARGETS])
    te, to, ve, vo = g.t_edges, g.t_off, g.v_edges, g.v_off
    cites = {}
    for i in range(g.n):
        if not cone[i] or g.kinds[i] != 'thm' or g.tsize[i] <= 12 or vo[i + 1] - vo[i] != 1 or RESTATE_SKIP.search(g.names[i]):
            continue
        a = ve[vo[i]]
        if (a != i and g.kinds[a] == 'thm' and g.thash[a] == g.thash[i] and g.tsize[a] == g.tsize[i]
                and g.vsize[i] <= g.tsize[i] + 40):
            cites[i] = a

    def original(i):
        seen = set()
        while i in cites and i not in seen:
            seen.add(i)
            i = cites[i]
        return i

    orig = {b: original(b) for b in cites}
    orig = {b: a for b, a in orig.items() if not g.names[a].startswith('_private.') and '«' not in g.names[a]}
    users, elsewhere = collections.defaultdict(set), set()
    for i in range(g.n):
        if not cone[i]:
            continue
        for j in te[to[i]:to[i + 1]]:
            if j in orig and j != i:
                elsewhere.add(j)
        proof = g.kinds[i] == 'thm'
        for j in ve[vo[i]:vo[i + 1]]:
            if j in orig and j != i:
                if proof:
                    users[j].add(i)
                else:
                    elsewhere.add(j)
    cand = {b for b in orig if b not in elsewhere and users.get(b)}
    say(f'{len(cites):,} restatements among what the five theorems need; {len(orig) - len(cand):,} left out '
        f'(the original is private, or the restatement is used in a statement or a definition)')
    files = {b: {g.mods[u] for u in users[b] if u not in cand} for b in cand}
    gain = {b: g.tsize[b] + g.vsize[b] for b in cand}
    order = sorted(cand, key=lambda b: -gain[b] / (1 + len(files[b])))
    picked, mods = [], set()
    for b in order:
        new = files[b] - mods
        if len(mods) + len(new) > max_files:
            continue
        mods |= new
        picked.append(b)
    say(f'{len(picked):,} restatements taken, {sum(gain[b] for b in picked):,} nodes if all of them leave; '
        f'{len(mods):,} files to edit')
    write_repoints(g, picked, orig, {b: [u for u in users[b] if u not in cand] for b in picked}, gain, out, say)


def gen_recite(out, max_files, skip_files=None, skip_names=None):
    """Like `repoint`, for any theorems with the same statement, however each is proved.

    Among the theorems the five need that share one statement, one is kept; another can go when every
    proof that uses it lies in a file that imports the kept one's file, since then that proof can cite
    the kept one instead. (A user that is itself one of those to go does not count.) The kept one is
    the member for which most can go. Users' files are edited; nothing is deleted.

    `skip_files`: modules that may not be edited (a batch already under way); `skip_names`: declarations
    already dealt with there."""
    t0 = time.time()

    def say(msg):
        print(f'{msg}  [{time.time() - t0:.0f}s]', flush=True)

    overlay_consts = os.path.join(C.DATA_OVERLAY, 'consts.tsv')
    g = CONE.load_graph(C.DATA_BASE, overlay_consts if os.path.exists(overlay_consts) else None, (), say)
    by = CONE.find_names(g, set(C.TARGETS))
    cone = CONE.reach(g, [by[t] for t in C.TARGETS])
    te, to, ve, vo = g.t_edges, g.t_off, g.v_edges, g.v_off
    groups = collections.defaultdict(list)
    for i in range(g.n):
        if cone[i] and g.kinds[i] == 'thm' and g.tsize[i] > 12 and not IFACE.AUX.search(g.names[i]) \
                and not RESTATE_SKIP.search(g.names[i]):
            groups[(g.thash[i], g.tsize[i])].append(i)
    groups = {k: v for k, v in groups.items() if len(v) > 1}
    member = {i: k for k, v in groups.items() for i in v}
    users, elsewhere = collections.defaultdict(set), set()
    aux = collections.Counter()
    for i in range(g.n):
        if not cone[i]:
            continue
        mm = IFACE.AUX.search(g.names[i])
        if mm:
            aux[(g.mods[i], g.names[i][:mm.start()])] += g.tsize[i] + g.vsize[i]
        for j in te[to[i]:to[i + 1]]:
            if j in member and j != i:
                elsewhere.add(j)
        proof = g.kinds[i] == 'thm'
        for j in ve[vo[i]:vo[i + 1]]:
            if j in member and j != i:
                if proof:
                    users[j].add(i)
                else:
                    elsewhere.add(j)
    closure, bit, _topo = import_closures(g, {g.mods[i] for i in member})
    say(f'{len(groups):,} statements with more than one theorem ({len(member):,} theorems)')

    def sees(u, o):
        mu, mo = g.mods[u], g.mods[o]
        return mu != mo and (closure[mu] >> bit[mo]) & 1

    skipn = skip_names or set()
    size = {i: g.tsize[i] + g.vsize[i] + aux.get((g.mods[i], g.names[i]), 0) for i in member}
    orig, real, gain = {}, {}, {}
    for key, members in groups.items():
        best = None
        for o in members:
            if g.names[o].startswith('_private.') or '«' in g.names[o]:
                continue
            go = {d for d in members if d != o and d not in elsewhere and users.get(d) and g.names[d] not in skipn}
            changed = True
            while changed and go:
                changed = False
                for d in list(go):
                    if any(u not in go and not sees(u, o) for u in users[d]):
                        go.discard(d)
                        changed = True
            if go:
                val = sum(size[d] for d in go)
                if best is None or val > best[0]:
                    best = (val, o, go)
        if best:
            _val, o, go = best
            for d in go:
                orig[d] = o
                real[d] = [u for u in users[d] if u not in go]
                gain[d] = size[d]
    say(f'{len(orig):,} theorems could go ({sum(gain.values()):,} nodes, their own helpers included), '
        f'cited through {len(set(orig.values())):,} kept ones')
    skipf = skip_files or set()
    files = {d: {g.mods[u] for u in real[d]} for d in orig}
    order = sorted((d for d in orig if not any(g.modnames[m] in skipf for m in files[d])),
                   key=lambda d: -gain[d] / (1 + len(files[d])))
    picked, mods = [], set()
    for d in order:
        new = files[d] - mods
        if len(mods) + len(new) > max_files:
            continue
        mods |= new
        picked.append(d)
    say(f'{len(picked):,} taken, {sum(gain[d] for d in picked):,} nodes if all of them leave; {len(mods):,} files to edit'
        + (f' ({len(orig) - len(order):,} left for later: a file they need is being edited by another batch)' if skipf else ''))
    write_repoints(g, picked, orig, real, gain, out, say)


def write_repoints(g, picked, orig, real_users, gain, out, say):
    """Edits that replace, in the source of every user in `real_users[b]`, the mentions of `b` by the full
    name of `orig[b]`; a `b` with a user that does not mention it by name is left out."""
    need = collections.defaultdict(lambda: collections.defaultdict(list))   # module -> restatement -> its users there
    for b in picked:
        for u in real_users[b]:
            need[g.mods[u]][b].append(u)
    names = {b: CD.user_name(g.names[b]) for b in picked}
    ranges = CD.load_ranges(g.patched)
    spans = collections.defaultdict(dict)                 # module -> restatement -> [(start, end, old, enclosing)]
    broken = collections.Counter()
    dead = set()
    modlist = sorted(need, key=lambda m: g.modnames[m])
    for lo in range(0, len(modlist), 2000):
        chunk = modlist[lo:lo + 2000]
        text = texts_at(accepted_commit(), [g.modnames[m] for m in chunk])
        for m in chunk:
            mn = g.modnames[m]
            src = text.get(mn)
            if src is None:
                dead |= set(need[m])
                broken['restatements used in a file whose source was not found'] += len(need[m])
                continue
            lines = src.split('\n')
            comments = comment_spans(src)
            for b, us in need[m].items():
                found, fine = set(), True
                for u in us:
                    nm, r = g.names[u], None
                    for _ in range(4):                    # a helper (`foo._proof_3`) lies in the range of `foo`
                        r = ranges.get((mn, nm))
                        if r is not None or '.' not in nm:
                            break
                        nm = nm.rsplit('.', 1)[0]
                    if r is None:
                        fine = False
                        broken['restatements with a user whose place in the source is not known'] += 1
                        break
                    here = mentions(src, CD.offset(lines, r[0], r[1]), CD.offset(lines, r[2], r[3]), names[b], comments)
                    if not here:
                        fine = False
                        broken['restatements with a user that does not mention the name plainly'] += 1
                        break
                    found.update((a0, a1, src[a0:a1], nm) for a0, a1 in here)
                if fine:
                    spans[m][b] = sorted(found)
                else:
                    dead.add(b)
    edits = []
    for m in modlist:
        for b, found in spans[m].items():
            if b in dead:
                continue
            for a0, a1, old, parent in found:
                edits.append({'module': g.modnames[m], 'theorem': parent or g.names[b],
                              'first_line': 0, 'first_col': a0, 'start': a0, 'end': a1,
                              'old_sha': hashlib.sha256(old.encode('utf-8')).hexdigest(),
                              'body': g.names[orig[b]], 'tag': 'repoint', 'size': gain[b], 'tokens': 0,
                              'drops': g.names[b]})
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    with open(out, 'w', encoding='utf-8') as fh:
        for e in edits:
            fh.write(json.dumps(e, ensure_ascii=False) + '\n')
    with open(out + '.pairs.tsv', 'w', encoding='utf-8') as fh:
        for b in picked:
            if b not in dead:
                fh.write(f'{g.names[b]}\t{g.names[orig[b]]}\t{gain[b]}\t{len({g.mods[u] for u in real_users[b]})}\n')
    for k, v in broken.items():
        print(f'  {k}: {v:,}')
    live = [b for b in picked if b not in dead]
    say(f'{len(edits):,} edits in {len({e["module"] for e in edits}):,} files for {len(live):,} restatements '
        f'({sum(gain[b] for b in live):,} nodes if all leave); written to {out}')


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


ALLOW_IMPORTS = False              # set for a batch of citations through added imports (--allow-imports)


def good(r):
    if not (r and r.get('ok')) or r.get('added') or r.get('sorry'):
        return False
    if r.get('compatible'):
        return True
    # An added import makes the comparison say "not compatible". In a batch of citations through added
    # imports that is expected; the judge decides whether each import meets the conditions.
    return bool(ALLOW_IMPORTS and r.get('imports_added') and not r.get('breaking') and not r.get('ext_changed')
                and not r.get('ns_removed'))


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
KEEP_EQUAL = False                 # set for edits whose gain is elsewhere (a restatement stops being needed): --keep-equal


def strict_tokens(text):
    """Source tokens of a text, as the source dial counts them: a dotted name is one token plus one for
    every numeric projection step in it, so `h.2.2.1` is four. (Before 2026-11-22 the dial counted such a
    name as one token and this function was the stricter count that bulk edits were held to.)"""
    return CONE.count_tokens(text)


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
        # Each file stands on its own. Its written-out size may not grow, and one of the two sizes must
        # fall. If its source grows (counting every projection step), the written-out size must fall by
        # at least EXCHANGE nodes per token added.
        before = strict_tokens(accepted[m]) if m in accepted else None
        paying = []
        for w, vid, used in options:
            old = res[(vid, m)].get('old_written_out')
            if old is None or before is None or w > old:
                continue
            with open(C.module_path(m, os.path.join(work, 'v', vid)), encoding='utf-8') as fh:
                added = strict_tokens(fh.read()) - before
            if added < 0 or (w < old and (added == 0 or old - w >= EXCHANGE * added)) or (KEEP_EQUAL and added == 0):
                paying.append((w, vid, used, added))
        if not paying:
            stats['files where nothing got smaller, or the gain does not pay for the added source'] += 1
            continue
        w, vid, used, added = min(paying, key=lambda o: (o[0], o[3]))
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
        try:
            with open(C.module_path(m, src), encoding='utf-8', newline='') as fh:
                touched = fh.read() != text[m]            # someone is working on this file: leave it
        except OSError:
            touched = True
        if failed or touched or (expect and hashlib.sha256(new.encode('utf-8')).hexdigest() != want[m]):
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
    ic = sub.add_parser('import-citations')
    ic.add_argument('--out', required=True)
    ic.add_argument('--min-proof-tokens', type=int, default=LONG_TOKENS + 1)
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
    us = sub.add_parser('unused-steps')
    us.add_argument('--out', required=True)
    us.add_argument('--table', required=True, help='module, declaration, nodes, names of unused local steps')
    us.add_argument('--max-modules', type=int, default=3000)
    rp = sub.add_parser('repoint')
    rp.add_argument('--out', required=True)
    rp.add_argument('--max-files', type=int, default=10000)
    rc = sub.add_parser('recite')
    rc.add_argument('--out', required=True)
    rc.add_argument('--max-files', type=int, default=10000)
    rc.add_argument('--skip-edits', default=None, nargs='*',
                    help='edit lists of batches under way: their files are not edited, their restatements not taken')
    v = sub.add_parser('variants')
    v.add_argument('--edits', required=True); v.add_argument('--work', required=True)
    v.add_argument('--single-from', default=None); v.add_argument('--modules', default=None)
    v.add_argument('--allow-imports', action='store_true')
    c = sub.add_parser('choose')
    c.add_argument('--edits', required=True); c.add_argument('--work', required=True)
    c.add_argument('--allow-imports', action='store_true')
    c.add_argument('--keep-equal', action='store_true',
                   help='keep a file whose sizes are unchanged (the gain is in what stops being needed)')
    a = sub.add_parser('apply')
    a.add_argument('--chosen', required=True)
    a.add_argument('--expect', default=None, help='W/final/sources.tsv: refuse unless the files come out byte-identical')
    a.add_argument('--drop-stale', action='store_true', help='leave out files that would not come out identical')
    args = ap.parse_args()
    if getattr(args, 'allow_imports', False):
        globals()['ALLOW_IMPORTS'] = True
    if args.cmd == 'import-citations':
        gen_import_citations(args.out, args.min_proof_tokens)
    elif args.cmd in ('citations', 'transplants'):
        gen(args.cmd, args.out, args.form, args.min_proof_tokens)
    elif args.cmd == 'shorten':
        gen_shorten(args.out, args.candidates)
    elif args.cmd == 'repoint':
        gen_repoint(args.out, args.max_files)
    elif args.cmd == 'recite':
        skip_files, skip_names = set(), set()
        for path in args.skip_edits or ():
            with open(path, encoding='utf-8') as fh:
                for line in fh:
                    e = json.loads(line)
                    skip_files.add(e['module'])
                    if e.get('drops'):
                        skip_names.add(e['drops'])
        gen_recite(args.out, args.max_files, skip_files, skip_names)
    elif args.cmd == 'unused-steps':
        gen_unused_steps(args.out, args.table, args.max_modules)
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
        if args.keep_equal:
            globals()['KEEP_EQUAL'] = True
        choose(args.edits, args.work)
    else:
        apply(args.chosen, expect=args.expect, drop_stale=args.drop_stale)


if __name__ == '__main__':
    main()
