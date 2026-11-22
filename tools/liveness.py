#!/usr/bin/env python3
"""Which inputs does the proof never use, and what would leave the cone without them?

  tools/liveness.py run    --out build/liveness/out.tsv     run tools/moddump's `liveness` over every module
  tools/liveness.py report --in  build/liveness/out.tsv     what removing the dead inputs would save, and where

The Lean tool (tools/moddump/Liveness.lean) finds, in the compiled proof, arguments of theorems that
neither statement nor proof mentions, the arguments passed in those places, and local `have`s that are not
used; each can make the others dead, so it works through the modules in dependency order. `report` puts
its output on top of the declaration graph and recomputes the cone of the five theorems: a declaration
that was only reached through a dead argument leaves it.

This is a measurement. Nothing is edited; turning a finding into a change means editing the source of the
theorem and of every place that uses it, and passing the judge.
"""
import argparse, collections, os, subprocess, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C
import cone as CONE

EXE = os.path.join(C.ROOT, 'tools', 'moddump', '.lake', 'build', 'bin', 'liveness')


def graph(say):
    overlay_consts = os.path.join(C.DATA_OVERLAY, 'consts.tsv')
    return CONE.load_graph(C.DATA_BASE, overlay_consts if os.path.exists(overlay_consts) else None, (), say)


def run(out):
    t0 = time.time()

    def say(msg):
        print(f'{msg}  [{time.time() - t0:.0f}s]', flush=True)

    g = graph(say)
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
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    lst = out + '.modules'
    with open(lst, 'w') as fh:
        for m in order:
            fh.write(f'{g.modnames[m]}\t{C.current_olean(g.modnames[m])}\n')
    say(f'{len(order):,} modules in dependency order; running the Lean tool')
    with open(lst, 'rb') as fin, open(out, 'wb') as fout:
        rc = subprocess.run([EXE], stdin=fin, stdout=fout).returncode
    say(f'done, exit code {rc}; output in {out}')
    return rc


def report(path, top):
    t0 = time.time()

    def say(msg):
        print(f'{msg}  [{time.time() - t0:.0f}s]', flush=True)

    g = graph(say)
    idx = g.idx
    by_name = CONE.find_names(g, set(C.TARGETS))
    roots = [by_name[t] for t in C.TARGETS]
    cone = CONE.reach(g, roots)
    old_total = sum(g.tsize[i] + g.vsize[i] for i in range(g.n) if cone[i])
    new_t, new_v, t_over, v_over = {}, {}, {}, {}
    info = {}
    passed = []
    errors = modules = mismatch = 0
    with open(path, 'rb') as fh:
        for line in fh:
            f = line.rstrip(b'\n').split(b'\t')
            if f[0] == b'L' and len(f) >= 15:
                i = idx.get(int(f[1]))
                if i is None:
                    continue
                tb, ta, vb, va = int(f[5]), int(f[6]), int(f[7]), int(f[8])
                if tb != g.tsize[i] or vb != g.vsize[i]:
                    mismatch += 1
                new_t[i], new_v[i] = ta, va
                t_over[i] = [idx[int(d)] for d in f[12].split(b' ') if d and int(d) in idx]
                v_over[i] = [idx[int(d)] for d in f[13].split(b' ') if d and int(d) in idx]
                info[i] = (f[2].decode(), int(f[3]), [int(x) for x in f[4].split(b',') if x], int(f[9]), int(f[10]),
                           int(f[11]))
            elif f[0] == b'D' and len(f) >= 6:
                passed.append((int(f[4]), int(f[3]), int(f[2]), f[5].decode('utf-8', 'replace')))
            elif f[0] == b'E':
                modules += 1
            elif f[0] == b'X':
                errors += 1
    say(f'{modules:,} modules read by the Lean tool, {errors} could not be read; {len(info):,} declarations with a finding; '
        f'sizes that differ from the tables: {mismatch}')
    te, to, ve, vo = g.t_edges, g.t_off, g.v_edges, g.v_off
    mark = bytearray(g.n)
    stack = list(roots)
    for r in stack:
        mark[r] = 1
    while stack:
        i = stack.pop()
        for j in (t_over[i] if i in t_over else te[to[i]:to[i + 1]]):
            if not mark[j]:
                mark[j] = 1; stack.append(j)
        for j in (v_over[i] if i in v_over else ve[vo[i]:vo[i + 1]]):
            if not mark[j]:
                mark[j] = 1; stack.append(j)
    new_total = shrink = 0
    left = []
    for i in range(g.n):
        if mark[i]:
            a = new_t.get(i, g.tsize[i]) + new_v.get(i, g.vsize[i])
            new_total += a
            shrink += g.tsize[i] + g.vsize[i] - a
        elif cone[i]:
            left.append(i)
    gone_nodes = sum(g.tsize[i] + g.vsize[i] for i in left)
    n_cone = sum(cone)
    in_cone = [i for i in info if cone[i]]
    with_dead = [i for i in in_cone if info[i][2]]
    print(f'cone before: {n_cone:,} declarations, {old_total:,} nodes')
    print(f'cone after:  {sum(mark):,} declarations, {new_total:,} nodes  '
          f'({old_total - new_total:,} fewer, {100 * (old_total - new_total) / old_total:.2f}%)')
    print(f'  inside declarations that stay: {shrink:,} nodes')
    print(f'  declarations that leave the cone: {len(left):,}, {gone_nodes:,} nodes')
    print(f'theorems in the cone with at least one dead argument: {len(with_dead):,} '
          f'({sum(len(info[i][2]) for i in with_dead):,} arguments)')
    print(f'dead arguments removed at uses: {sum(info[i][3] for i in in_cone):,}; unused haves removed: '
          f'{sum(info[i][4] for i in in_cone):,}; uses with too few arguments to tell: {sum(info[i][5] for i in in_cone):,}')
    passed.sort(reverse=True)
    print(f'\nwhere the most is passed in a dead place (nodes, times, position, theorem), top {top}:')
    for w, n, pos, nm in passed[:top]:
        print(f'  {w:>12,}  {n:>6}  #{pos:<3} {nm}')
    by_area = collections.Counter()
    for i in left:
        by_area['.'.join(g.modnames[g.mods[i]].split('.')[:3])] += g.tsize[i] + g.vsize[i]
    print(f'\nwhat leaves the cone, by area (nodes), top {top}:')
    for a, w in by_area.most_common(top):
        print(f'  {w:>12,}  {a}')
    left.sort(key=lambda i: -(g.tsize[i] + g.vsize[i]))
    print(f'\nlargest declarations that leave the cone, top {top}:')
    for i in left[:top]:
        print(f'  {g.tsize[i] + g.vsize[i]:>12,}  {g.names[i]}')
    stay = sorted(((g.tsize[i] + g.vsize[i] - new_t[i] - new_v[i], i) for i in info if mark[i]), reverse=True)
    print(f'\nlargest savings inside one declaration that stays, top {top}:')
    for d, i in stay[:top]:
        k, depth, dead, a, h, s = info[i]
        print(f'  {d:>12,}  {g.names[i]}  (dead arguments {dead or "-"}, removed at uses {a}, haves {h})')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('command', choices=['run', 'report'])
    ap.add_argument('--out', default=os.path.join(C.ROOT, 'build', 'liveness', 'out.tsv'))
    ap.add_argument('--in', dest='inp', default=os.path.join(C.ROOT, 'build', 'liveness', 'out.tsv'))
    ap.add_argument('--top', type=int, default=25)
    a = ap.parse_args()
    if a.command == 'run':
        sys.exit(run(a.out))
    report(a.inp, a.top)


if __name__ == '__main__':
    main()
