#!/usr/bin/env python3
"""What do the five theorems actually ask of each declaration?

  tools/demand.py tables --out build/demand/tables.tsv [--jobs 40]
  tools/demand.py sweep  --tables build/demand/tables.tsv --out build/demand/sweep1.tsv [--params build/demand/sweep0.tsv] [--jobs 40]
  tools/demand.py report --in build/demand/sweep1.tsv [--top 30]

The Lean tool (tools/moddump/Demand.lean) follows the demand from the targets down through the compiled
proof terms: which parts of a conjunction, which fields of a record, which arguments and which local
`have`s are read by something that is itself needed. `tables` collects what it must know in advance
(in parallel, any order). `sweep` runs it once over the modules of the cone, each module before everything
it imports; a second sweep can use what the first learned about arguments (`--params`), and can only find
more. `report` puts the result on the declaration graph: what stays, what leaves, and where the largest
unneeded parts are.

A measurement only. Nothing is edited.
"""
import argparse, collections, os, subprocess, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C
import cone as CONE

EXE = os.path.join(C.ROOT, 'tools', 'moddump', '.lake', 'build', 'bin', 'demand')


def graph(say):
    overlay_consts = os.path.join(C.DATA_OVERLAY, 'consts.tsv')
    return CONE.load_graph(C.DATA_BASE, overlay_consts if os.path.exists(overlay_consts) else None, (), say)


def timer():
    t0 = time.time()

    def say(msg):
        print(f'{msg}  [{time.time() - t0:.0f}s]', flush=True)
    return say


def dependency_order(g):
    """Modules with every module after what it imports."""
    midx = {m: k for k, m in enumerate(g.modnames)}
    imports = [[midx[x] for x in imps if x in midx] for imps in g.mod_imports]
    order, state = [], bytearray(len(g.modnames))
    for root in range(len(g.modnames)):
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
    return order


def tables(out, jobs):
    say = timer()
    g = graph(say)
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    lines = [f'{m}\t{C.current_olean(m)}\n' for m in g.modnames]
    procs = []
    for k in range(jobs):
        part = f'{out}.in{k}'
        with open(part, 'w') as fh:
            fh.writelines(lines[k::jobs])
        procs.append(subprocess.Popen([EXE, '--tables'], stdin=open(part, 'rb'), stdout=open(f'{out}.out{k}', 'wb')))
    bad = sum(1 for p in procs if p.wait() != 0)
    counts = collections.Counter()
    with open(out, 'wb') as fo:
        for k in range(jobs):
            with open(f'{out}.out{k}', 'rb') as fh:
                for line in fh:
                    counts[line[:1].decode()] += 1
                    if line[:1] not in (b'E',):
                        fo.write(line)
            os.remove(f'{out}.out{k}')
            os.remove(f'{out}.in{k}')
    say(f'tables written to {out}: {dict(counts)}; processes that failed: {bad}')
    return 1 if bad else 0


def sweep(tables_path, out, params, threads):
    say = timer()
    g = graph(say)
    by_name = CONE.find_names(g, set(C.TARGETS))
    cone = CONE.reach(g, [by_name[t] for t in C.TARGETS])
    in_cone = bytearray(len(g.modnames))
    for i in range(g.n):
        if cone[i]:
            in_cone[g.mods[i]] = 1
    # level of a module: 0 if nothing imports it, else one more than the deepest module that imports it.
    # Computed over every module (a module outside the cone can sit between two modules of the cone).
    midx = {m: k for k, m in enumerate(g.modnames)}
    order = dependency_order(g)
    level = [0] * len(g.modnames)
    for m in reversed(order):                       # importers before what they import
        for x in g.mod_imports[m]:
            i = midx.get(x)
            if i is not None and level[i] < level[m] + 1:
                level[i] = level[m] + 1
    by_level = collections.defaultdict(list)
    for m in range(len(g.modnames)):
        if in_cone[m]:
            by_level[level[m]].append(m)
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    lst = out + '.modules'
    n = 0
    with open(lst, 'w') as fh:
        for lv in sorted(by_level):
            for m in by_level[lv]:
                fh.write(f'{g.modnames[m]}\t{C.current_olean(g.modnames[m])}\n')
                n += 1
            fh.write('-\n')
    cmd = [EXE, '--sweep', tables_path, '--roots', ','.join(C.TARGETS), '--threads', str(threads)]
    if params:
        p = out + '.params'
        with open(params, 'rb') as fi, open(p, 'wb') as fo:
            k = 0
            for line in fi:
                if line[:2] == b'P\t':
                    fo.write(line)
                    k += 1
        cmd += ['--params', p]
        say(f'{k:,} theorems with an argument that is not fully needed, from {params}')
    sizes = sorted(len(v) for v in by_level.values())
    say(f'{n:,} modules of the cone in {len(by_level):,} levels (largest level {sizes[-1]:,}, median {sizes[len(sizes) // 2]}); '
        f'running the Lean tool with {threads} workers')
    with open(lst, 'rb') as fin, open(out, 'wb') as fout:
        rc = subprocess.run(cmd, stdin=fin, stdout=fout).returncode
    say(f'done, exit code {rc}; output in {out}')
    return rc


def report(path, top):
    say = timer()
    g = graph(say)
    idx = g.idx
    by_name = CONE.find_names(g, set(C.TARGETS))
    cone = CONE.reach(g, [by_name[t] for t in C.TARGETS])
    alive = bytearray(g.n)
    dead_in = {}
    info = {}
    partial = []
    given_up = modules = errors = unknown = 0
    with open(path, 'rb') as fh:
        for line in fh:
            f = line.rstrip(b'\n').split(b'\t')
            tag = f[0]
            if tag == b'A':
                i = idx.get(int(f[1]))
                if i is None:
                    unknown += 1
                else:
                    alive[i] = 1
            elif tag == b'V' and len(f) >= 10:
                i = idx.get(int(f[1]))
                if i is not None:
                    dead_in[i] = int(f[5])
                    info[i] = (int(f[6]), int(f[7]), int(f[8]))
            elif tag == b'Q' and len(f) >= 4:
                i = idx.get(int(f[1]))
                if i is not None:
                    partial.append((i, f[2].decode()))
            elif tag == b'G':
                given_up += 1
            elif tag == b'E':
                modules += 1
            elif tag == b'X':
                errors += 1
    say(f'{modules:,} modules read, {errors} failed; analysis given up in {given_up:,} declarations; '
        f'needed declarations not in the tables: {unknown}')
    old_total = sum(g.tsize[i] + g.vsize[i] for i in range(g.n) if cone[i])
    n_cone = sum(cone)
    stay = [i for i in range(g.n) if alive[i] and cone[i]]
    outside = sum(1 for i in range(g.n) if alive[i] and not cone[i])
    left = [i for i in range(g.n) if cone[i] and not alive[i]]
    inside = sum(dead_in.get(i, 0) for i in stay)
    new_total = sum(g.tsize[i] + g.vsize[i] for i in stay) - inside
    gone = sum(g.tsize[i] + g.vsize[i] for i in left)
    print(f'cone before: {n_cone:,} declarations, {old_total:,} nodes')
    print(f'needed:      {len(stay):,} declarations, {new_total:,} nodes  '
          f'({old_total - new_total:,} fewer, {100 * (old_total - new_total) / old_total:.2f}%)')
    print(f'  declarations nothing needed asks for: {len(left):,}, {gone:,} nodes')
    print(f'  inside declarations that stay: {inside:,} nodes in {sum(1 for i in stay if dead_in.get(i))} declarations')
    print(f'  components not needed: {sum(v[0] for v in info.values()):,}; haves: {sum(v[1] for v in info.values()):,}; '
          f'arguments: {sum(v[2] for v in info.values()):,}; theorems asked for only part of their result: {len(partial):,}')
    if outside:
        print(f'  (needed declarations outside the old cone: {outside}; should be 0)')
    # a statement is needed whole, so everything a needed statement mentions must be needed too;
    # anything else means a declaration was looked at before all its users had been
    te, to = g.t_edges, g.t_off
    late = sum(1 for i in range(g.n) if alive[i] for j in te[to[i]:to[i + 1]] if not alive[j])
    print(f'  check: references from needed statements to declarations not marked needed: {late} (should be 0)')
    by_area = collections.Counter()
    for i in left:
        by_area['.'.join(g.modnames[g.mods[i]].split('.')[:3])] += g.tsize[i] + g.vsize[i]
    print(f'\nwhat nothing asks for, by area (nodes), top {top}:')
    for a, w in by_area.most_common(top):
        print(f'  {w:>13,}  {a}')
    left.sort(key=lambda i: -(g.tsize[i] + g.vsize[i]))
    print(f'\nlargest declarations nothing asks for, top {top}:')
    for i in left[:top]:
        print(f'  {g.tsize[i] + g.vsize[i]:>13,}  {g.kinds[i]}  {g.names[i]}')
    # Where to cut: a declaration that stays mentions one that leaves, in a part nothing needs. Removing
    # that mention (weakening the statement or deleting the unneeded step) frees everything that is
    # reached only through it. For each such entry point: what it reaches among the declarations that leave.
    ve, vo = g.v_edges, g.v_off
    gone_set = set(left)
    entry = collections.defaultdict(set)
    for i in stay:
        for j in ve[vo[i]:vo[i + 1]]:
            if j in gone_set:
                entry[j].add(i)
    weight = {i: g.tsize[i] + g.vsize[i] for i in left}
    reach = []
    for r in sorted(entry, key=lambda r: -weight[r])[:3000]:
        seen, stack, w = {r}, [r], 0
        while stack:
            x = stack.pop()
            w += weight[x]
            for y in list(te[to[x]:to[x + 1]]) + list(ve[vo[x]:vo[x + 1]]):
                if y in gone_set and y not in seen:
                    seen.add(y)
                    stack.append(y)
        reach.append((w, len(seen), r))
    reach.sort(reverse=True)
    print(f'\nentry points: {len(entry):,} declarations that leave are mentioned by one that stays. '
          f'Largest by what they reach among the leaving (nodes, declarations, entry point <- mentioned in), top {top}:')
    for w, n, r in reach[:top]:
        users = sorted(entry[r], key=lambda i: -g.vsize[i])
        print(f'  {w:>13,}  {n:>7,}  {g.names[r]}  <-  {g.names[users[0]]}' + (f' (+{len(users) - 1} more)' if len(users) > 1 else ''))
    big = sorted(((dead_in[i], i) for i in stay if dead_in.get(i)), reverse=True)
    print(f'\nlargest unneeded parts inside a declaration that stays, top {top}:')
    for d, i in big[:top]:
        c, h, a = info[i]
        print(f'  {d:>13,} of {g.vsize[i]:>11,}  {g.names[i]}  (components {c}, haves {h}, arguments {a})')
    part = {i: s for i, s in partial}
    print(f'\ntheorems asked for only part of their result, largest first, top {top}:')
    for i in sorted(part, key=lambda i: -g.vsize[i])[:top]:
        print(f'  {g.vsize[i]:>13,}  {g.names[i]}  {part[i][:90]}')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('command', choices=['tables', 'sweep', 'report'])
    ap.add_argument('--out', default=None)
    ap.add_argument('--tables', default=os.path.join(C.ROOT, 'build', 'demand', 'tables.tsv'))
    ap.add_argument('--params', default=None)
    ap.add_argument('--in', dest='inp', default=None)
    ap.add_argument('--jobs', type=int, default=40)
    ap.add_argument('--top', type=int, default=30)
    a = ap.parse_args()
    if a.command == 'tables':
        sys.exit(tables(a.out or a.tables, a.jobs))
    if a.command == 'sweep':
        sys.exit(sweep(a.tables, a.out or os.path.join(C.ROOT, 'build', 'demand', 'sweep1.tsv'), a.params, a.jobs))
    report(a.inp or os.path.join(C.ROOT, 'build', 'demand', 'sweep1.tsv'), a.top)


if __name__ == '__main__':
    main()
