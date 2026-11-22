#!/usr/bin/env python3
"""Compile alternative versions of files side by side and check each one.

  tools/batch_variants.py --plan W/plan_all.tsv --work W --jobs 80 [--time-accepted 500]

The plan lists `<variant>\t<module>`; the source of a variant is W/v/<variant>/<module path>.lean
(written by tools/proof_edits.py). Each is compiled against the accepted state into
W/out/<variant>/ and compared with the module's accepted compiled form by the equivalence check.
One JSON line per variant goes to W/results.jsonl, with the module's written-out size before and
after, so a run can be watched and resumed.

--time-accepted N also compiles the accepted version of N randomly chosen modules of the plan under
the same load, so that a time before and after exists for those.

Nothing under proof/src is touched. Meant for a rented machine (GRH_NO_SANDBOX=1 there).
"""
import argparse, json, os, random, subprocess, sys, threading, time
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C
import iface as IFACE


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--plan', required=True)
    ap.add_argument('--work', required=True)
    ap.add_argument('--jobs', type=int, default=8)
    ap.add_argument('--mem-gb', type=float, default=16.0)
    ap.add_argument('--timeout', type=int, default=1800)
    ap.add_argument('--time-accepted', type=int, default=0)
    ap.add_argument('--seed', type=int, default=1)
    a = ap.parse_args()
    os.environ['GRH_SLOTS'] = str(a.jobs)
    from compile_one import compile_module

    work = os.path.abspath(a.work)
    results_path = os.path.join(work, 'results.jsonl')
    done = {}
    if os.path.exists(results_path):
        with open(results_path) as fh:
            for line in fh:
                try:
                    r = json.loads(line)
                    done[(r['variant'], r['module'])] = r
                except ValueError:
                    pass
    with open(a.plan) as fh:
        plan = [tuple(l.rstrip('\n').split('\t')[:2]) for l in fh if l.strip()]
    todo = [p for p in plan if p not in done]
    state = C.accepted_state()
    commit = state['proof_commit'] if state else C.UPSTREAM_TAG
    mods = sorted({m for _, m in plan})
    random.Random(a.seed).shuffle(mods)
    timed = set(mods[:a.time_accepted])
    print(f'{len(plan)} variants, {len(done)} already done, {len(todo)} to compile, {a.jobs} at a time'
          + (f'; timing the accepted version of {len(timed)} modules' if timed else ''), flush=True)
    lock = threading.Lock()
    t0 = time.time()
    n = [0, 0]
    old_times = {}

    def size_of(decls):
        return sum(r['tsize'] + r['vsize'] for r in decls.values())

    def work_one(p):
        vid, m = p
        rec = {'variant': vid, 'module': m}
        try:
            out = os.path.join(work, 'out', vid)
            r = compile_module(m, out, src=os.path.join(work, 'v', vid), overlays=[], mem_gb=a.mem_gb,
                               timeout=a.timeout, quiet=True)
            rec.update({'ok': r['ok'], 'time_s': r.get('time_s'), 'wall_s': r.get('wall_s'),
                        'sorry': r.get('mentions_sorry')})
            if r['ok']:
                res, old, new = IFACE.check_module(m, out)
                rec.update({'compatible': res['compatible'], 'breaking': res['breaking'][:5],
                            'added': [x for x in res['added'] if not IFACE.AUX.search(x)][:5],
                            'aux_to_check': len(res['aux_to_check']), 'strict': res.get('strict'),
                            'ext_changed': res.get('ext_changed'), 'ns_removed': res.get('ns_removed'),
                            'imports_added': res.get('imports_added'),
                            'old_written_out': size_of(old), 'written_out': size_of(new)})
            else:
                rec['error'] = (r.get('messages_tail') or r.get('error') or '')[-500:]
            if m in timed:                               # once per module, with whichever variant comes first
                with lock:
                    need = m not in old_times
                    if need:
                        old_times[m] = None
                if need:
                    rel = 'src/' + m.replace('.', '/') + '.lean'
                    text = subprocess.run(['git', '-C', C.PROOF, 'show', f'{commit}:{rel}'], stdout=subprocess.PIPE,
                                          check=True).stdout
                    src = C.module_path(m, os.path.join(work, 'oldsrc'))
                    os.makedirs(os.path.dirname(src), exist_ok=True)
                    with open(src, 'wb') as fh:
                        fh.write(text)
                    ro = compile_module(m, os.path.join(work, 'old'), src=os.path.join(work, 'oldsrc'), overlays=[],
                                        mem_gb=a.mem_gb, timeout=a.timeout, quiet=True)
                    if ro['ok']:
                        rec['old_time_s'] = ro.get('time_s')
                    for ext in ('.olean', '.ilean'):
                        try:
                            os.remove(C.module_path(m, os.path.join(work, 'old'), ext))
                        except OSError:
                            pass
        except Exception as e:                           # noqa: keep the batch going
            rec.update({'ok': False, 'error': f'exception: {e}'})
        with lock:
            with open(results_path, 'a') as fh:
                fh.write(json.dumps(rec) + '\n')
            n[0] += 1
            n[1] += 1 if rec.get('ok') and rec.get('compatible') else 0
            if n[0] % 200 == 0:
                el = time.time() - t0
                print(f'{n[0]}/{len(todo)} done, {n[1]} good, {el:.0f}s, {n[0] / el * 3600:.0f} per hour', flush=True)

    with ThreadPoolExecutor(max_workers=a.jobs) as pool:
        list(pool.map(work_one, todo))
    print(f'finished: {n[1]} good of {len(todo)} compiled now; {time.time() - t0:.0f}s', flush=True)


if __name__ == '__main__':
    main()
