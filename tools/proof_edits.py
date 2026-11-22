#!/usr/bin/env python3
"""Replace the proofs of chosen theorems, trying alternatives side by side and keeping what passes.

An edit is: in this module, replace everything after the `:=` that ends this theorem's statement by
this text. The statement itself is never touched. Edits are generated from the tables (a citation
of a copy the file already imports, or the text of the shortest proof of the same statement found
elsewhere), so they are guesses: each one has to compile and pass the equivalence check.

  tools/proof_edits.py citations  --out build/x/edits.jsonl [--form first|short] [--min-proof-tokens N]
  tools/proof_edits.py transplants --out build/x/edits.jsonl
  tools/proof_edits.py shorten     --out build/x/edits.jsonl    # shorten citations already recorded
  tools/proof_edits.py variants --edits E --work W [--single-from W/results.jsonl]
  tools/proof_edits.py choose   --edits E --work W            # after tools/batch_variants.py ran
  tools/proof_edits.py apply    --chosen W/chosen.jsonl       # write the chosen edits into proof/src

Variants. For every module, `variants` writes the file with all its edits applied (variant `all`)
under W/v/all/. Files are always built from the accepted commit, never from the working tree.
tools/batch_variants.py compiles each variant and checks it. With --single-from, a module whose
`all` variant failed and has several edits gets one variant per edit (`e0`, `e1`, ...), and later
`combine` gets the ones that passed on their own. `choose` then keeps, per module, the passing
variant that removes the most, records exactly which edits it contains (W/chosen.jsonl), and
gathers its compiled files under W/final/new for the judge.

Because every file is rebuilt from the accepted commit and the edit list, applying the chosen
edits on another machine gives byte-identical files.
"""
import argparse, collections, json, os, re, shutil, subprocess, sys, time

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
            n_unplaced += len(failed)
            if len(failed) < len(es):
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
          + (f'; {n_unplaced} edits could not be placed' if n_unplaced else ''))


def choose(edits_path, work):
    per = load_edits(edits_path)
    res = load_results(os.path.join(work, 'results.jsonl'))
    final = os.path.join(work, 'final', 'new')
    shutil.rmtree(os.path.join(work, 'final'), ignore_errors=True)
    os.makedirs(final)
    chosen, stats = [], collections.Counter()
    times = {}
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
        w, vid, used = min(options, key=lambda o: o[0])
        r = res[(vid, m)]
        if r.get('old_written_out') is not None and w >= r['old_written_out']:
            stats['files where nothing got smaller'] += 1
            continue
        stats['files kept'] += 1
        stats['edits kept'] += len(used)
        stats['written-out before'] += r.get('old_written_out') or 0
        stats['written-out after'] += w
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
    for k, v in stats.items():
        print(f'  {k}: {v:,}')
    print(f'chosen edits: {os.path.join(work, "chosen.jsonl")}; compiled files: {final}')


def apply(chosen_path, src=C.SRC):
    per = load_edits(chosen_path)
    text = texts_at(accepted_commit(), sorted(per))
    n = 0
    for m, es in sorted(per.items()):
        new, failed = apply_edits(text[m], es)
        if failed:
            sys.exit(f'{m}: {len(failed)} edit(s) could not be placed; is the accepted state the one they were made for?')
        with open(C.module_path(m, src), 'w', encoding='utf-8', newline='') as fh:
            fh.write(new)
        n += len(es)
    print(f'applied {n} edits in {len(per)} files')


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
    v = sub.add_parser('variants')
    v.add_argument('--edits', required=True); v.add_argument('--work', required=True)
    v.add_argument('--single-from', default=None); v.add_argument('--modules', default=None)
    c = sub.add_parser('choose')
    c.add_argument('--edits', required=True); c.add_argument('--work', required=True)
    a = sub.add_parser('apply')
    a.add_argument('--chosen', required=True)
    args = ap.parse_args()
    if args.cmd in ('citations', 'transplants'):
        gen(args.cmd, args.out, args.form, args.min_proof_tokens)
    elif args.cmd == 'shorten':
        gen_shorten(args.out, args.candidates)
    elif args.cmd == 'variants':
        os.makedirs(args.work, exist_ok=True)
        variants(args.edits, args.work, args.single_from, args.modules)
    elif args.cmd == 'choose':
        choose(args.edits, args.work)
    else:
        apply(args.chosen)


if __name__ == '__main__':
    main()
