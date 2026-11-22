#!/usr/bin/env python3
"""Spot check of the claim behind the equivalence check: recompile files that USE changed modules.

  tools/downstream_check.py --new build/batch/new --sample 300 --jobs 40 [--control] [--seed 1]
  tools/downstream_check.py --new build/batch/new --modules FILE --jobs 40      (exactly the listed files)

The judge does not rebuild files that import a changed module when the module still exposes the
same statements. This tool tests that on a sample: it takes files that directly import at least
one module found under --new, compiles each against the accepted state with the modules under
--new swapped in, and compares the result with the file's accepted compiled form, declaration by
declaration, proofs included, plus what the file registers with Lean.

If the changed modules really look the same from outside, every sampled file must compile to
exactly what it was. `--control` compiles the same sample without the swap, which shows whether a
plain recompile is reproducible on this machine at all (it should be).

Needs room for many compiles at once; meant for a rented machine (GRH_NO_SANDBOX=1 there).
"""
import argparse, json, os, random, sys, threading, time
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C
import nscheck as NS

FIELDS = ('kind', 'tsize', 'vsize', 'thash', 'vhash', 'st', 'sv', 'lp')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--new', required=True, help='root of the recompiled (changed) modules')
    ap.add_argument('--sample', type=int, default=300)
    ap.add_argument('--jobs', type=int, default=8)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--control', action='store_true', help='compile the sample without swapping anything in')
    ap.add_argument('--exclude', default=None,
                    help='file with modules never to sample (for instance files that are being rewritten themselves)')
    ap.add_argument('--modules', default=None,
                    help='check exactly the modules listed in this file, not a sample (changed modules are left out)')
    ap.add_argument('--work', default=None,
                    help="with --modules: the batch's work directory. A listed module that is itself changed is "
                         'then compiled again from its chosen text, with every other changed module in place, and '
                         'compared with its compiled form under --new (it was first compiled without them)')
    ap.add_argument('--out', default=os.path.join(C.ROOT, 'build', 'downstream'))
    ap.add_argument('--mem-gb', type=float, default=16.0)
    a = ap.parse_args()
    os.environ['GRH_SLOTS'] = str(a.jobs)
    from compile_one import compile_module

    new_root = os.path.abspath(a.new)
    changed = set()
    for dp, dn, fn in os.walk(new_root):
        for f in fn:
            if f.endswith('.olean'):
                changed.add(os.path.relpath(os.path.join(dp, f), new_root)[:-6].replace(os.sep, '.'))
    imports, _ = NS.load()
    skip = set(changed)
    if a.exclude:
        with open(a.exclude) as fh:
            skip |= {l.strip() for l in fh if l.strip()}
    variant = {}
    if a.work:
        with open(os.path.join(a.work, 'final', 'sources.tsv')) as fh:
            for l in fh:
                m, vid, _ = l.rstrip('\n').split('\t')
                variant[m] = vid
    if a.modules:
        with open(a.modules) as fh:
            listed = {l.strip() for l in fh if l.strip()}
        sample = sorted(m for m in listed if m not in changed or m in variant)
        print(f'{len(changed)} changed modules; checking the {len(sample)} listed files '
              f'({sum(1 for m in sample if m in changed)} of them changed files, compiled again from their new text)'
              + (' (control: nothing swapped in)' if a.control else ''), flush=True)
    else:
        users = sorted(m for m, imps in imports.items() if m not in skip and any(i in changed for i in imps))
        random.Random(a.seed).shuffle(users)
        sample = users[:a.sample]
        print(f'{len(changed)} changed modules; {len(users)} files import at least one of them directly; '
              f'checking {len(sample)}' + (' (control: nothing swapped in)' if a.control else ''), flush=True)

    out = os.path.abspath(a.out) + ('_control' if a.control else '')
    os.makedirs(out, exist_ok=True)
    lock = threading.Lock()
    results = []
    t0 = time.time()

    def work(m):
        rec = {'module': m}
        try:
            if m in changed:
                r = compile_module(m, out, src=os.path.join(a.work, 'v', variant[m]), overlays=[new_root],
                                   mem_gb=a.mem_gb, quiet=True)
                ref = C.module_path(m, new_root, '.olean')
            else:
                r = compile_module(m, out, overlays=[] if a.control else [new_root], mem_gb=a.mem_gb, quiet=True)
                ref = C.current_olean(m)
            rec['ok'] = r['ok']
            if not r['ok']:
                rec['error'] = (r.get('messages_tail') or r.get('error') or '')[-400:]
            else:
                parsed = C.parse_consts(C.moddump([(m + '@old', ref), (m + '@new', r['olean'])]))
                o, n = parsed[m + '@old'], parsed[m + '@new']
                diff = []
                for name in sorted(set(o['decls']) | set(n['decls'])):
                    x, y = o['decls'].get(name), n['decls'].get(name)
                    if x is None or y is None:
                        diff.append(f'{name}: only in the {"new" if x is None else "accepted"} version')
                    else:
                        d = [k for k in FIELDS if x.get(k) != y.get(k)]
                        if d:
                            diff.append(f'{name}: {",".join(d)}')
                ext = {k: [o['ext'].get(k, 0), n['ext'].get(k, 0)] for k in set(o['ext'] or {}) | set(n['ext'] or {})
                       if (o['ext'] or {}).get(k, 0) != (n['ext'] or {}).get(k, 0)}
                rec.update({'declarations': len(o['decls']), 'different': diff[:10], 'different_count': len(diff),
                            'registers_differently': ext,
                            'namespaces_differ': sorted(set(o['namespaces'] or ()) ^ set(n['namespaces'] or ()))})
                for ext_ in ('.olean', '.ilean'):
                    try:
                        os.remove(C.module_path(m, out, ext_))
                    except OSError:
                        pass
        except Exception as e:                           # noqa: keep going
            rec.update({'ok': False, 'error': f'exception: {e}'})
        with lock:
            results.append(rec)
            if len(results) % 50 == 0:
                print(f'{len(results)}/{len(sample)} done, {time.time() - t0:.0f}s', flush=True)

    with ThreadPoolExecutor(max_workers=a.jobs) as pool:
        list(pool.map(work, sample))
    json.dump(results, open(os.path.join(out, 'results.json'), 'w'), indent=1)
    failed = [r for r in results if not r.get('ok')]
    same = [r for r in results if r.get('ok') and not r['different_count'] and not r['registers_differently']
            and not r['namespaces_differ']]
    other = [r for r in results if r.get('ok') and r not in same]
    print(f'identical to the accepted compiled form: {len(same)} of {len(results)}; '
          f'different: {len(other)}; did not compile: {len(failed)}; {time.time() - t0:.0f}s')
    for r in other[:10]:
        print('  different:', r['module'], r['different'][:3], r['registers_differently'], r['namespaces_differ'])
    for r in failed[:10]:
        print('  did not compile:', r['module'], r.get('error', '')[-300:].replace('\n', ' | '))
    sys.exit(0 if not other and not failed else 2)


if __name__ == '__main__':
    main()
