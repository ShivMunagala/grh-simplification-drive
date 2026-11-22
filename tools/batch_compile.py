#!/usr/bin/env python3
"""Compile many already-edited files in parallel and check each one, on a machine with room for it.

  tools/batch_compile.py --modules list.txt --out build/batch --jobs 80

For every module in the list (one per line; the file must already be edited in proof/src):
compile it against the accepted state, then run the equivalence check against its accepted version.
One JSON line per module goes to <out>/results.jsonl as it finishes, so a run can be watched and
resumed (modules already in results.jsonl are skipped).

At the end, for the modules that compiled and kept their interface, the table rows that the judge
needs are written to <out>/consts.tsv and <out>/decls.tsv, next to the compiled files in <out>/new.

Meant for a rented machine with many cores and enough memory to keep the compiled base in the
page cache; run with GRH_NO_SANDBOX=1 there. Files that fail are left as they are: the caller
decides whether to restore them.
"""
import argparse, json, os, sys, threading, time
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C
import iface as IFACE


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--modules', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--jobs', type=int, default=8)
    ap.add_argument('--mem-gb', type=float, default=16.0)
    ap.add_argument('--timeout', type=int, default=1800)
    a = ap.parse_args()
    os.environ['GRH_SLOTS'] = str(a.jobs)
    from compile_one import compile_module          # after GRH_SLOTS is set

    out = os.path.abspath(a.out)
    new_dir = os.path.join(out, 'new')
    os.makedirs(new_dir, exist_ok=True)
    results_path = os.path.join(out, 'results.jsonl')
    done = {}
    if os.path.exists(results_path):
        with open(results_path) as fh:
            for line in fh:
                try:
                    r = json.loads(line)
                    done[r['module']] = r
                except ValueError:
                    pass
    with open(a.modules) as fh:
        modules = [l.strip() for l in fh if l.strip()]
    todo = [m for m in modules if m not in done]
    print(f'{len(modules)} modules, {len(done)} already done, {len(todo)} to compile, {a.jobs} at a time', flush=True)

    lock = threading.Lock()
    t0 = time.time()
    counter = [0, 0]                                 # finished, good

    def work(m):
        try:
            r = compile_module(m, new_dir, overlays=[], mem_gb=a.mem_gb, timeout=a.timeout, quiet=True)
            rec = {'module': m, 'ok': r['ok'], 'time_s': r.get('time_s'), 'cpu_s': r.get('cpu_s'),
                   'wall_s': r.get('wall_s'), 'max_rss_mb': r.get('max_rss_mb'), 'sorry': r.get('mentions_sorry')}
            if r['ok']:
                res, old, new = IFACE.check_module(m, new_dir)
                rec.update({'compatible': res['compatible'], 'breaking': res['breaking'][:5],
                            'added': [n for n in res['added'] if not IFACE.AUX.search(n)][:5],
                            'aux_to_check': len(res['aux_to_check'])})
            else:
                rec['error'] = (r.get('messages_tail') or r.get('error') or '')[-400:]
        except Exception as e:                       # noqa: keep the batch going
            rec = {'module': m, 'ok': False, 'error': f'exception: {e}'}
        with lock:
            with open(results_path, 'a') as fh:
                fh.write(json.dumps(rec) + '\n')
            counter[0] += 1
            counter[1] += 1 if rec.get('ok') and rec.get('compatible') else 0
            if counter[0] % 200 == 0:
                el = time.time() - t0
                print(f'{counter[0]}/{len(todo)} done, {counter[1]} good, {el:.0f}s, '
                      f'{counter[0] / el * 3600:.0f} per hour', flush=True)
            done[m] = rec

    with ThreadPoolExecutor(max_workers=a.jobs) as pool:
        list(pool.map(work, todo))

    good = [m for m in modules if done.get(m, {}).get('ok') and done[m].get('compatible')
            and not done[m].get('added') and not done[m].get('sorry')]
    with open(os.path.join(out, 'good.txt'), 'w') as fh:
        fh.write('\n'.join(good) + ('\n' if good else ''))
    with open(os.path.join(out, 'consts.tsv'), 'wb') as fh:
        for i in range(0, len(good), 2000):
            chunk = good[i:i + 2000]
            fh.write(b'\n'.join(C.moddump([(m, C.module_path(m, new_dir, '.olean')) for m in chunk])))
            fh.write(b'\n')
    with open(os.path.join(out, 'decls.tsv'), 'w', encoding='utf-8') as fh:
        for m in good:
            d = C.load_json(C.module_path(m, new_dir, '.ilean'), {}) or {}
            for name, r in (d.get('decls') or {}).items():
                fh.write(f'{m}\t{r[0]}\t{r[1]}\t{r[2]}\t{r[3]}\t{name}\n')
    print(f'finished: {len(good)} good of {len(modules)}; {time.time() - t0:.0f}s', flush=True)


if __name__ == '__main__':
    main()
