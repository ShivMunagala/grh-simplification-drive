#!/usr/bin/env python3
"""Can the imports that a change adds alter how any other file is read?

  tools/import_visibility.py --chosen build/W/chosen.jsonl --work build/W --out build/W/visibility [--jobs 8]

A file that gains an import makes the imported module visible to every file that imports it, directly or
not. The judge allows such an import only when the module registers nothing that acts on other files
(iface.plain_module): no instances, no simp or other tagged lemmas, no notation, no coercions. What is left
is names. An identifier in some other file could now resolve to a declaration of the newly visible module:
a new candidate in an open or enclosing namespace, a name that now hides one further out, or a new target
for dot notation.

This tool rules that out file by file. For every file G and every module X that becomes visible to G
through the added imports, it looks in G's source for an identifier component equal to the last component
of a declaration of X whose parent is not itself declared in X. (A declaration under a parent declared in X,
such as a constructor, a field or an auxiliary definition, can only be reached by naming the parent or
opening its namespace, and then the parent's own last component is in G.) Without such a component, no
name in G can resolve to anything in X, and X cannot change how G is read.

The files with a hit are written to <out>/flagged.txt, to be checked exactly: recompiled against the changed
state and compared with their accepted compiled form (tools/downstream_check.py --modules).

A changed file is checked as well, on its new text, for the modules it gains through other changed files:
it was compiled before those were visible to it.

Needs several gigabytes of memory for the import closures.
"""
import argparse, collections, json, os, re, sys, time
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C
import cone as CONE

WORD = re.compile(r"[^\W\d][\w'!?]*")
KEYS = None


def words_of(job):
    """(module, path) -> (module, words of the source that are last components of declarations to watch)"""
    m, path = job
    try:
        with open(path, encoding='utf-8') as fh:
            text = fh.read()
    except OSError:
        return m, None
    found = set(WORD.findall(CONE.strip_comments(text)))
    return m, sorted(found & KEYS)


def main():
    global KEYS
    ap = argparse.ArgumentParser()
    ap.add_argument('--chosen', required=True, help='chosen.jsonl of a batch: the edits, with the imports they add')
    ap.add_argument('--work', default=None, help="the batch's work directory; changed files are read from its variants")
    ap.add_argument('--out', required=True)
    ap.add_argument('--jobs', type=int, default=8)
    a = ap.parse_args()
    t0 = time.time()

    def say(msg):
        print(f'{msg}  [{time.time() - t0:.0f}s]', flush=True)

    added = collections.defaultdict(set)
    with open(a.chosen) as fh:
        for l in fh:
            e = json.loads(l)
            for x in e.get('imports') or ():
                added[e['module']].add(x)
    variant = {}
    if a.work:
        src = os.path.join(a.work, 'final', 'sources.tsv')
        if os.path.exists(src):
            for l in open(src):
                m, vid, _ = l.rstrip('\n').split('\t')
                variant[m] = vid
    overlay_consts = os.path.join(C.DATA_OVERLAY, 'consts.tsv')
    g = CONE.load_graph(C.DATA_BASE, overlay_consts if os.path.exists(overlay_consts) else None, (), say)
    modnames = g.modnames
    n = len(modnames)
    midx = {m: k for k, m in enumerate(modnames)}
    old = [[midx[x] for x in imps if x in midx] for imps in g.mod_imports]
    new = []
    for k in range(n):
        extra = [midx[x] for x in added.get(modnames[k], ()) if x in midx]
        new.append(old[k] + [x for x in extra if x not in old[k]])
    order, state = [], bytearray(n)
    for root in range(n):
        if state[root]:
            continue
        stack = [(root, iter(new[root]))]
        state[root] = 1
        while stack:
            m, it = stack[-1]
            for i in it:
                if state[i] == 1:                    # still on the stack: an import cycle
                    sys.exit(f'the added imports close a cycle through {modnames[i]}')
                if not state[i]:
                    state[i] = 1
                    stack.append((i, iter(new[i])))
                    break
            else:
                stack.pop()
                state[m] = 2
                order.append(m)
    c_old, c_new = [0] * n, [0] * n
    for m in order:
        c = 0
        for i in old[m]:
            c |= c_old[i] | (1 << i)
        c_old[m] = c
        c = 0
        for i in new[m]:
            c |= c_new[i] | (1 << i)
        c_new[m] = c
    gains = {}                                   # module -> bitset of modules it newly sees and was not compiled with
    for m in range(n):
        nv = c_new[m] ^ c_old[m]                 # the old closure is part of the new one
        if nv:
            own = 0
            for x in added.get(modnames[m], ()):
                if x in midx:
                    own |= 1 << midx[x]
            nv &= ~own
            if nv:
                gains[m] = nv
    del c_old, c_new
    seen_new = 0
    for nv in gains.values():
        seen_new |= nv
    xs = [k for k in range(n) if (seen_new >> k) & 1]
    say(f'{len(added):,} files gain imports ({sum(len(v) for v in added.values()):,} in all); '
        f'{len(gains):,} files see a module they did not see before; {len(xs):,} modules become visible somewhere')

    # declarations of the newly visible modules: last components to watch
    xset = set(xs)
    names = collections.defaultdict(list)
    for i in range(g.n):
        if g.mods[i] in xset:
            nm = g.names[i]
            if not nm.startswith('_private.'):
                names[g.mods[i]].append(nm)
    watch = collections.defaultdict(set)          # last component -> modules declaring it at their top level
    n_top = 0
    for x, ns in names.items():
        have = set(ns)
        for nm in ns:
            k = nm.rfind('.')
            parent, last = (nm[:k], nm[k + 1:]) if k >= 0 else ('', nm)
            if parent in have or last.isdigit() or not last:
                continue
            watch[last.strip('«»')].add(x)
            n_top += 1
    KEYS = frozenset(watch)
    say(f'{n_top:,} declarations to watch in those modules, {len(KEYS):,} distinct last components')

    jobs = []
    for m in gains:
        name = modnames[m]
        root = os.path.join(a.work, 'v', variant[name]) if name in variant and a.work else C.SRC
        jobs.append((m, C.module_path(name, root)))
    hits = {}
    missing = 0
    with Pool(a.jobs) as pool:
        for m, found in pool.imap_unordered(words_of, jobs, chunksize=200):
            if found is None:
                missing += 1
                continue
            nv = gains[m]
            bad = {}
            for w in found:
                for x in watch[w]:
                    if (nv >> x) & 1:
                        bad.setdefault(x, []).append(w)
            if bad:
                hits[m] = bad
    say(f'sources read: {len(jobs) - missing:,} (missing: {missing}); files with a name that could reach a newly '
        f'visible module: {len(hits):,}')
    os.makedirs(a.out, exist_ok=True)
    flagged = sorted(modnames[m] for m in hits)
    with open(os.path.join(a.out, 'flagged.txt'), 'w') as fh:
        fh.write(''.join(m + '\n' for m in flagged))
    by_word = collections.Counter()
    with open(os.path.join(a.out, 'hits.tsv'), 'w', encoding='utf-8') as fh:
        for m in sorted(hits, key=lambda k: modnames[k]):
            for x, ws in sorted(hits[m].items()):
                fh.write(f'{modnames[m]}\t{modnames[x]}\t{" ".join(sorted(ws)[:12])}\n')
                for w in ws:
                    by_word[w] += 1
    changed_flagged = [m for m in flagged if m in added]
    json.dump({'files_gaining_imports': len(added), 'files_seeing_new_modules': len(gains),
               'modules_newly_visible': len(xs), 'declarations_watched': n_top, 'flagged_files': len(flagged),
               'flagged_changed_files': len(changed_flagged), 'flagged_pairs': sum(len(v) for v in hits.values()),
               'commonest_words': by_word.most_common(25)},
              open(os.path.join(a.out, 'summary.json'), 'w'), indent=1)
    print(f'flagged: {len(flagged):,} files ({len(changed_flagged):,} of them changed files), '
          f'{sum(len(v) for v in hits.values()):,} file-module pairs; commonest words: {by_word.most_common(12)}')
    print(f'written: {a.out}/flagged.txt, hits.tsv, summary.json')


if __name__ == '__main__':
    main()
