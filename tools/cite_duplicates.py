#!/usr/bin/env python3
"""Statements proved more than once: find them, and make a copy cite another copy it already imports.

  tools/cite_duplicates.py find  --out build/cite            # from the tables, about a minute
  tools/cite_duplicates.py apply --list build/cite/candidates.tsv [--limit N] [--modules FILE]

find
  Groups the theorems the five targets depend on by statement. A group with two or more members
  that do not cite each other is the same statement proved independently. For every such copy it
  looks for another copy that the copy's file already imports, directly or not (or that stands
  earlier in the same file). Those are the candidates: the proof can be replaced by a citation
  without touching any import, so no other file sees a difference.

  Statements are matched with Lean's own hash plus size, which can collide and ignores argument
  names. That is good enough to propose a candidate: a wrong match does not compile, and the
  statement of the edited theorem is not touched at all.

  Writes <out>/candidates.tsv (largest first) and <out>/summary.json, which also counts the copies
  that see no other copy: those need a shared file that both import, a larger change.

apply
  Rewrites the listed theorems in proof/src: everything after the `:=` that ends the statement
  is replaced by

      by first | exact @C | exact C | (intros; apply C <;> assumption)

  where C is the cited copy. This is the form the archive itself uses for its restating theorems.
  The statement is kept character for character. Files are compiled and checked afterwards
  (tools/batch_compile.py); a file that fails is restored by the caller.
"""
import argparse, collections, json, os, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C
import cone as CONE
import iface as IFACE

HEADER = ['written_out', 'statement_size', 'module', 'theorem', 'cite', 'cite_module',
          'first_line', 'first_col', 'last_line', 'last_col']


def load_ranges(replaced):
    ranges = {}
    overlay = os.path.join(C.DATA_OVERLAY, 'decls.tsv')
    for path, is_base in ((os.path.join(C.DATA_BASE, 'decls.tsv.zst'), True), (overlay, False)):
        if not os.path.exists(path):
            continue
        for line in CONE.zlines(path):
            f = line.rstrip(b'\n').split(b'\t', 5)
            if len(f) == 6:
                m = f[0].decode()
                if is_base and m in replaced:
                    continue
                ranges[(m, f[5].decode('utf-8', 'replace'))] = (int(f[1]), int(f[2]), int(f[3]), int(f[4]))
    return ranges


def user_name(name):
    """`_private.Some.Module.0.Foo.bar` -> `Foo.bar`; other names unchanged."""
    if not name.startswith('_private.'):
        return name
    parts = name.split('.')
    for k, p in enumerate(parts):
        if p == '0' and k > 0:
            return '.'.join(parts[k + 1:])
    return name


def find(out):
    t0 = time.time()

    def say(msg):
        print(f'{msg}  [{time.time() - t0:.0f}s]', flush=True)

    overlay_consts = os.path.join(C.DATA_OVERLAY, 'consts.tsv')
    g = CONE.load_graph(C.DATA_BASE, overlay_consts if os.path.exists(overlay_consts) else None, (), say)
    by_name = CONE.find_names(g, set(C.TARGETS))
    cone = CONE.reach(g, [by_name[t] for t in C.TARGETS])
    ranges = load_ranges(g.patched)
    say(f'cone: {sum(cone)} declarations; source ranges: {len(ranges)}')

    groups = collections.defaultdict(list)
    n_thm = 0
    for i in range(g.n):
        if cone[i] and g.kinds[i] == 'thm' and not IFACE.AUX.search(g.names[i]):
            n_thm += 1
            groups[(g.thash[i], g.tsize[i])].append(i)
    ve, vo = g.v_edges, g.v_off
    indep = []                                        # groups with >= 2 members that cite no other member
    citing = 0
    for key, members in groups.items():
        if len(members) < 2:
            continue
        mset = set(members)
        roots = [i for i in members if not ((set(ve[vo[i]:vo[i + 1]]) & mset) - {i})]
        citing += len(members) - len(roots)
        if len(roots) > 1:
            indep.append((key, roots))
    say(f'{n_thm} theorems, {len(groups)} distinct statements; {len(indep)} statements proved independently more than once')

    # which modules does each module import, directly or not? (bit sets over the modules that hold a copy)
    modnames, mod_imports = g.modnames, g.mod_imports
    midx = {m: k for k, m in enumerate(modnames)}
    holders = sorted({g.mods[i] for _, roots in indep for i in roots})
    bit = {m: k for k, m in enumerate(holders)}
    imports = [[midx[x] for x in imps if x in midx] for imps in mod_imports]
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
    say('import closures done')

    # written-out size of a theorem with the auxiliaries that belong to it (same module, name below it)
    aux_size = collections.Counter()
    for i in range(g.n):
        if cone[i] and IFACE.AUX.search(g.names[i]):
            nm = g.names[i]
            aux_size[(g.mods[i], nm[:IFACE.AUX.search(nm).start()])] += g.tsize[i] + g.vsize[i]

    rows = []
    tot = collections.Counter()
    for key, roots in indep:
        ms = sorted(roots, key=lambda i: (topo[g.mods[i]], g.names[i]))
        for pos, d in enumerate(ms):
            tot['copies'] += 1
            md = g.mods[d]
            rd = ranges.get((modnames[md], g.names[d]))
            cost = g.vsize[d] + aux_size.get((md, g.names[d]), 0)
            target = None
            for c in ms:
                if c == d:
                    continue
                mc = g.mods[c]
                if mc != md:
                    if (closure[md] >> bit[mc]) & 1 and not g.names[c].startswith('_private.'):
                        target = c
                        break
                elif rd is not None:
                    rc = ranges.get((modnames[mc], g.names[c]))
                    if rc is not None and (rc[2], rc[3]) <= (rd[0], rd[1]):       # earlier in the same file
                        target = c
                        break
            if target is not None and rd is not None:
                tot['copies that can cite a copy they already see'] += 1
                tot['their written-out size'] += cost
                rows.append((cost, key[1], modnames[md], g.names[d], g.names[target], modnames[g.mods[target]]) + rd)
            elif target is not None:
                tot['copies that see another copy but have no source range'] += 1
            elif pos > 0:
                tot['copies that see no other copy and are not the earliest'] += 1
                tot['written-out size of those'] += cost
            else:
                tot['earliest copies (kept)'] += 1
    rows.sort(key=lambda r: (-r[0], r[2], r[3]))
    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, 'candidates.tsv'), 'w', encoding='utf-8') as fh:
        fh.write('\t'.join(HEADER) + '\n')
        for r in rows:
            fh.write('\t'.join(str(x) for x in r) + '\n')
    summary = {'cone_theorems': n_thm, 'distinct_statements': len(groups),
               'statements_proved_independently_more_than_once': len(indep),
               'theorems_that_already_cite_a_copy': citing,
               'candidate_files': len({r[2] for r in rows}), **tot}
    json.dump(summary, open(os.path.join(out, 'summary.json'), 'w'), indent=1)
    for k, v in summary.items():
        print(f'  {k}: {v:,}')
    say(f'candidates written to {os.path.join(out, "candidates.tsv")}')


def statement_end(text):
    """Index just after the first `:=` outside brackets, comments and strings, or None."""
    depth, i, n = 0, 0, len(text)
    while i < n:
        ch = text[i]
        two = text[i:i + 2]
        if two == '--':
            j = text.find('\n', i)
            i = n if j < 0 else j
            continue
        if two == '/-':
            level, i = 1, i + 2
            while i < n and level:
                if text[i:i + 2] == '/-':
                    level, i = level + 1, i + 2
                elif text[i:i + 2] == '-/':
                    level, i = level - 1, i + 2
                else:
                    i += 1
            continue
        if ch == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            i += 1
            continue
        if ch in '([{⟨':
            depth += 1
        elif ch in ')]}⟩':
            depth -= 1
        elif two == ':=' and depth == 0:
            return i + 2
        i += 1
    return None


def offset(lines, line, col):
    """Character offset in '\\n'.join(lines) of (0-based line, UTF-16 column)."""
    return sum(len(l) + 1 for l in lines[:line]) + CONE.u16_index(lines[line], col)


def apply(list_path, limit, modules_file, src=C.SRC):
    want = None
    if modules_file:
        with open(modules_file) as fh:
            want = {l.strip() for l in fh if l.strip()}
    per_file = collections.defaultdict(list)
    with open(list_path, encoding='utf-8') as fh:
        head = fh.readline().rstrip('\n').split('\t')
        for line in fh:
            r = dict(zip(head, line.rstrip('\n').split('\t')))
            if want is None or r['module'] in want:
                per_file[r['module']].append(r)
    done = skipped = 0
    edited = []
    for module, rs in per_file.items():
        if limit and done >= limit:
            break
        path = C.module_path(module, src)
        try:
            with open(path, encoding='utf-8', newline='') as fh:
                text = fh.read()
        except OSError:
            skipped += len(rs)
            continue
        lines = text.split('\n')
        edits = []
        for r in rs:
            a = offset(lines, int(r['first_line']), int(r['first_col']))
            b = offset(lines, int(r['last_line']), int(r['last_col']))
            decl = text[a:b]
            short = user_name(r['theorem']).split('.')[-1]
            k = statement_end(decl)
            if k is None or short not in decl[:k] or not any(w in decl[:k] for w in ('theorem', 'lemma')):
                skipped += 1
                continue
            cite = r['cite']
            cname = user_name(cite) if cite.startswith('_private.') else '_root_.' + cite
            body = f' by first | exact @{cname} | exact {cname} | (intros; apply {cname} <;> assumption)'
            edits.append((a + k, b, body, r))
        if not edits:
            continue
        edits.sort(key=lambda e: e[0], reverse=True)
        last_start = len(text) + 1
        for a, b, body, r in edits:
            if b > last_start:                      # overlapping ranges: leave the outer one alone
                skipped += 1
                continue
            text = text[:a] + body + text[b:]
            last_start = a
            done += 1
            edited.append((module, r['theorem'], r['cite']))
        with open(path, 'w', encoding='utf-8', newline='') as fh:
            fh.write(text)
    print(f'rewrote {done} theorems in {len({m for m, _, _ in edited})} files; skipped {skipped}')
    return edited


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    f = sub.add_parser('find')
    f.add_argument('--out', default=os.path.join(C.ROOT, 'build', 'cite'))
    a = sub.add_parser('apply')
    a.add_argument('--list', required=True)
    a.add_argument('--limit', type=int, default=0)
    a.add_argument('--modules', default=None, help='only these modules (file, one per line)')
    a.add_argument('--edited', default=None, help='write module, theorem, cited copy of every rewrite to this file')
    args = ap.parse_args()
    if args.cmd == 'find':
        find(args.out)
    else:
        edited = apply(args.list, args.limit, args.modules)
        if args.edited:
            with open(args.edited, 'w', encoding='utf-8') as fh:
                for row in edited:
                    fh.write('\t'.join(row) + '\n')


if __name__ == '__main__':
    main()
