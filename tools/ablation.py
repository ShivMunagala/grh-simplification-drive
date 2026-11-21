#!/usr/bin/env python3
"""Rank declarations by how much of the cone depends only on them.

  tools/ablation.py [--data data/base] [--out data/base] [--rh-only]

For every declaration D in the cone this computes what would leave the cone if D were no longer
needed: the declarations that the target theorems reach only through D. (In graph terms: the
subtree below D in the dominator tree of the dependency graph, rooted at the targets.)

Two things come out of it:

  spine    declarations that everything below them passes through. Each one is a single statement
           from which the targets follow without looking at anything else underneath: a waist.
  blocks   for any declaration, the size of what hangs only on it. A known theorem with a large
           block is an expensive input; finding a way around it removes the whole block.

Mutually dependent declarations (a structure with its constructor and projections, for example)
are treated as one unit.

Outputs: <out>/ablation.tsv.zst, and a printed summary.
"""
import argparse, array, json, os, subprocess, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C
import cone as CONE


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--data', default=C.DATA_BASE)
    ap.add_argument('--out', default=None)
    ap.add_argument('--rh-only', action='store_true')
    ap.add_argument('--top', type=int, default=40)
    a = ap.parse_args()
    out = a.out or a.data
    t0 = time.time()

    def say(m):
        print(f'{m}  [{time.time() - t0:.0f}s]', flush=True)

    g = CONE.load_graph(a.data, say=say)
    targets = CONE.RH_ONLY if a.rh_only else C.TARGETS
    by_name = CONE.find_names(g, targets)
    roots = [by_name[t] for t in targets]
    n = g.n
    te, to, ve, vo = g.t_edges, g.t_off, g.v_edges, g.v_off

    def succ(i):
        return list(te[to[i]:to[i + 1]]) + list(ve[vo[i]:vo[i + 1]])

    # --- strongly connected components (iterative Tarjan) over what the roots reach
    index = array.array('i', [-1]) * n
    low = array.array('i', [0]) * n
    comp = array.array('i', [-1]) * n
    onstack = bytearray(n)
    stack = []
    comps = []                 # members of each component, emitted dependencies-first
    counter = 0
    for r in roots:
        if index[r] != -1:
            continue
        work = [(r, succ(r), 0)]
        index[r] = low[r] = counter; counter += 1
        stack.append(r); onstack[r] = 1
        while work:
            v, sv, k = work[-1]
            if k < len(sv):
                w = sv[k]
                work[-1] = (v, sv, k + 1)
                if index[w] == -1:
                    index[w] = low[w] = counter; counter += 1
                    stack.append(w); onstack[w] = 1
                    work.append((w, succ(w), 0))
                elif onstack[w] and index[w] < low[v]:
                    low[v] = index[w]
            else:
                work.pop()
                if work:
                    u = work[-1][0]
                    if low[v] < low[u]:
                        low[u] = low[v]
                if low[v] == index[v]:
                    members = []
                    while True:
                        w = stack.pop(); onstack[w] = 0
                        comp[w] = len(comps)
                        members.append(w)
                        if w == v:
                            break
                    comps.append(members)
    nc = len(comps)
    say(f'cone: {counter} declarations in {nc} units')

    # --- dominator tree on the acyclic graph of units; virtual root = nc
    ROOT = nc
    idom = array.array('i', [-1]) * (nc + 1)
    depth = array.array('i', [0]) * (nc + 1)
    idom[ROOT] = ROOT
    for r in roots:
        idom[comp[r]] = ROOT
    steps = 0
    for c in range(nc - 1, -1, -1):          # users before what they use
        d = idom[c]
        depth[c] = depth[d] + 1
        for v in comps[c]:
            for w in succ(v):
                cw = comp[w]
                if cw == c:
                    continue
                x = idom[cw]
                if x == -1:
                    idom[cw] = c
                elif x != c:
                    # nearest common ancestor of x and c in the tree built so far
                    y = c
                    while x != y:
                        if depth[x] > depth[y]:
                            x = idom[x]
                        else:
                            y = idom[y]
                        steps += 1
                    idom[cw] = x
    say(f'dominator tree built ({steps} ancestor steps)')

    # --- sizes of what hangs on each unit
    own_n = array.array('q', [0]) * (nc + 1)
    own_w = array.array('q', [0]) * (nc + 1)
    for c, members in enumerate(comps):
        own_n[c] = len(members)
        own_w[c] = sum(g.tsize[v] + g.vsize[v] for v in members)
    sub_n = array.array('q', own_n)
    sub_w = array.array('q', own_w)
    for c in range(nc):                       # dependencies first, so children are complete
        d = idom[c]
        sub_n[d] += sub_n[c]; sub_w[d] += sub_w[c]
    total_n, total_w = sub_n[ROOT], sub_w[ROOT]

    def rep(c):
        """Representative declaration of a unit: the shortest name."""
        return min(comps[c], key=lambda v: len(g.names[v]))

    def row(c):
        v = rep(c)
        d = idom[c]
        return {'name': g.names[v], 'kind': g.kinds[v], 'module': g.modnames[g.mods[v]],
                'unit_size': own_n[c], 'statement_size': g.tsize[v],
                'hangs_declarations': sub_n[c], 'hangs_written_out': sub_w[c],
                'share_of_cone': round(sub_w[c] / total_w, 4), 'depth': depth[c],
                'through': g.names[rep(d)] if d != ROOT else '(targets)'}

    # spine: follow, from the targets down, the child that carries most of what remains
    children = {}
    for c in range(nc):
        children.setdefault(idom[c], []).append(c)
    spine = []
    cur = ROOT
    while True:
        kids = children.get(cur, [])
        if not kids:
            break
        best = max(kids, key=lambda c: sub_w[c])
        if sub_w[best] < 0.5 * (sub_w[cur] if cur != ROOT else total_w):
            break
        spine.append(best)
        cur = best
    spine_set = set(spine)

    order = sorted(range(nc), key=lambda c: -sub_w[c])
    blocks = [c for c in order if c not in spine_set][:a.top]

    # Known theorems. In this tree a known result is stated as a named proposition
    # (`def GlobalTheory.Published.X : Prop := ...`) and proved by a theorem whose statement is
    # exactly that name. What hangs only on that proof is what the known result costs on its own.
    best = {}
    n_statements = set()
    for i in range(n):
        if comp[i] == -1:
            continue
        if g.kinds[i] == 'def' and 'Published.' in g.names[i]:
            n_statements.add(i)
        if g.kinds[i] != 'thm' or g.tsize[i] != 1 or to[i + 1] - to[i] != 1:
            continue
        j = te[to[i]]
        if 'Published.' in g.names[j]:
            c = comp[i]
            if j not in best or sub_w[c] > sub_w[best[j]]:
                best[j] = c
    published = sorted(best.items(), key=lambda kv: -sub_w[kv[1]])
    published_total_w = sum(sub_w[c] for c in set(best.values()))

    z = subprocess.Popen(['zstd', '-q', '-3', '-f', '-o', os.path.join(out, 'ablation.tsv.zst')], stdin=subprocess.PIPE)
    z.stdin.write(b'hangs_written_out\thangs_declarations\tshare_of_cone\tdepth\tunit_size\tkind\tmodule\tname\tthrough\n')
    for c in order[:200000]:
        r = row(c)
        z.stdin.write((f"{r['hangs_written_out']}\t{r['hangs_declarations']}\t{r['share_of_cone']}\t{r['depth']}\t"
                       f"{r['unit_size']}\t{r['kind']}\t{r['module']}\t{r['name']}\t{r['through']}\n").encode())
    z.stdin.close(); z.wait()

    def prow(j, c):
        r = row(c)
        r['statement'] = g.names[j]
        return r

    res = {'targets': targets, 'cone_declarations': total_n, 'cone_written_out': total_w, 'units': nc,
           'spine': [row(c) for c in spine],
           'largest_blocks': [row(c) for c in blocks],
           'known_statements_in_cone': len(n_statements),
           'known_statements_with_proof_found': len(best),
           'known_total_share_upper_bound': round(published_total_w / total_w, 4),
           'known': [prow(j, c) for j, c in published]}
    json.dump(res, open(os.path.join(out, 'ablation_rh.json' if a.rh_only else 'ablation.json'), 'w'), indent=1)

    def show(title, cs):
        print(f'\n{title}')
        for c in cs:
            r = row(c)
            print(f"  {100 * r['share_of_cone']:6.2f}%  {r['hangs_declarations']:>9} decls  depth {r['depth']:>3}  "
                  f"{r['kind']:<4} {r['name'][:110]}")

    print(f'\ncone: {total_n} declarations, written-out size {total_w}')
    show('SPINE (each line: everything below passes through this declaration)', spine)
    show(f'LARGEST BLOCKS off the spine (top {a.top})', blocks)
    print(f'\nKNOWN THEOREMS: {len(n_statements)} named statements in the cone, proof found for {len(best)}; '
          f'what hangs only on those proofs: at most {100 * published_total_w / total_w:.1f}% of the cone (top {a.top})')
    for j, c in published[:a.top]:
        r = row(c)
        print(f"  {100 * r['share_of_cone']:6.2f}%  {r['hangs_declarations']:>9} decls  "
              f"{g.names[j].replace('GlobalTheory.Published.', '')[:60]:<60} <- {r['name'][:70]}")
    say('done')


if __name__ == '__main__':
    main()
