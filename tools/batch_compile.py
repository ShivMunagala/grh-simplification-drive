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


def time_accepted(a, out, after, load, compile_module):
    """Compile the accepted version of each module (source from the accepted commit) and note its time."""
    import shutil, subprocess
    state = C.accepted_state()
    commit = state['proof_commit'] if state else C.UPSTREAM_TAG
    before_path = os.path.join(out, 'before.jsonl')
    before = load(before_path)
    oldsrc, old_dir = os.path.join(out, 'oldsrc'), os.path.join(out, 'old')
    with open(a.modules) as fh:
        modules = [l.strip() for l in fh if l.strip()]
    if a.sample:
        import random
        pool_ = sorted(m for m in modules if after.get(m, {}).get('ok') and after[m].get('compatible'))
        random.Random(a.seed).shuffle(pool_)
        modules = pool_[:a.sample]
    todo = [m for m in modules if m not in before]
    print(f'{len(modules)} modules, {len(before)} already timed, {len(todo)} accepted versions to compile, '
          f'{a.jobs} at a time', flush=True)
    lock = threading.Lock()
    t0 = time.time()
    n = [0]

    def work(m):
        rel = 'src/' + m.replace('.', '/') + '.lean'
        try:
            text = subprocess.run(['git', '-C', C.PROOF, 'show', f'{commit}:{rel}'], stdout=subprocess.PIPE,
                                  check=True).stdout
            src = C.module_path(m, oldsrc)
            os.makedirs(os.path.dirname(src), exist_ok=True)
            with open(src, 'wb') as fh:
                fh.write(text)
            r = compile_module(m, old_dir, src=oldsrc, overlays=[], mem_gb=a.mem_gb, timeout=a.timeout, quiet=True)
            rec = {'module': m, 'ok': r['ok'], 'time_s': r.get('time_s'), 'wall_s': r.get('wall_s')}
            for ext in ('.olean', '.ilean'):             # only the time is wanted
                try:
                    os.remove(C.module_path(m, old_dir, ext))
                except OSError:
                    pass
        except Exception as e:                           # noqa: keep the batch going
            rec = {'module': m, 'ok': False, 'error': f'exception: {e}'}
        with lock:
            with open(before_path, 'a') as fh:
                fh.write(json.dumps(rec) + '\n')
            before[m] = rec
            n[0] += 1
            if n[0] % 200 == 0:
                el = time.time() - t0
                print(f'{n[0]}/{len(todo)} timed, {el:.0f}s, {n[0] / el * 3600:.0f} per hour', flush=True)

    with ThreadPoolExecutor(max_workers=a.jobs) as pool:
        list(pool.map(work, todo))
    times = {m: {'before': before[m]['time_s'], 'after': after[m]['time_s']} for m in modules
             if before.get(m, {}).get('ok') and after.get(m, {}).get('ok')
             and before[m].get('time_s') is not None and after[m].get('time_s') is not None}
    json.dump(times, open(os.path.join(out, 'times.json'), 'w'))
    tb, ta = sum(t['before'] for t in times.values()), sum(t['after'] for t in times.values())
    print(f'finished: {len(times)} modules timed before and after; total {tb:.0f}s -> {ta:.0f}s; '
          f'{time.time() - t0:.0f}s', flush=True)
    shutil.rmtree(oldsrc, ignore_errors=True)


def time_paired(a, out, after, load, compile_module):
    """Time the accepted and the edited version of the same files back to back, so both see the same load."""
    import random, shutil, subprocess
    state = C.accepted_state()
    commit = state['proof_commit'] if state else C.UPSTREAM_TAG
    path = os.path.join(out, 'paired.jsonl')
    done = load(path)
    with open(a.modules) as fh:
        modules = [l.strip() for l in fh if l.strip()]
    pool_ = sorted(m for m in modules if after.get(m, {}).get('ok') and after[m].get('compatible'))
    random.Random(a.seed).shuffle(pool_)
    sample = pool_[:a.paired]
    todo = [m for m in sample if m not in done]
    print(f'{len(sample)} modules to time both ways, {len(done)} already done, {a.jobs} at a time', flush=True)
    oldsrc = os.path.join(out, 'paired_oldsrc')
    lock = threading.Lock()
    t0 = time.time()
    n = [0]

    def work(m):
        rel = 'src/' + m.replace('.', '/') + '.lean'
        rec = {'module': m}
        try:
            text = subprocess.run(['git', '-C', C.PROOF, 'show', f'{commit}:{rel}'], stdout=subprocess.PIPE,
                                  check=True).stdout
            src = C.module_path(m, oldsrc)
            os.makedirs(os.path.dirname(src), exist_ok=True)
            with open(src, 'wb') as fh:
                fh.write(text)
            order = ['old', 'new'] if hash(m) % 2 else ['new', 'old']     # half the pairs in each order
            for which in order:
                if which == 'old':
                    r = compile_module(m, os.path.join(out, 'paired_old'), src=oldsrc, overlays=[], mem_gb=a.mem_gb,
                                       timeout=a.timeout, quiet=True)
                else:
                    r = compile_module(m, os.path.join(out, 'paired_new'), overlays=[], mem_gb=a.mem_gb,
                                       timeout=a.timeout, quiet=True)
                rec[which] = r.get('time_s') if r['ok'] else None
                rec[which + '_wall'] = r.get('wall_s')
            for d in ('paired_old', 'paired_new'):
                for ext in ('.olean', '.ilean'):
                    try:
                        os.remove(C.module_path(m, os.path.join(out, d), ext))
                    except OSError:
                        pass
        except Exception as e:                           # noqa: keep going
            rec['error'] = f'exception: {e}'
        with lock:
            with open(path, 'a') as fh:
                fh.write(json.dumps(rec) + '\n')
            done[m] = rec
            n[0] += 1
            if n[0] % 100 == 0:
                print(f'{n[0]}/{len(todo)} pairs, {time.time() - t0:.0f}s', flush=True)

    with ThreadPoolExecutor(max_workers=a.jobs) as pool:
        list(pool.map(work, todo))
    times = {m: {'before': done[m]['old'], 'after': done[m]['new']} for m in sample
             if done.get(m, {}).get('old') is not None and done[m].get('new') is not None}
    json.dump(times, open(os.path.join(out, 'times.json'), 'w'))
    tb, ta = sum(t['before'] for t in times.values()), sum(t['after'] for t in times.values())
    print(f'finished: {len(times)} modules timed both ways back to back; total {tb:.0f}s -> {ta:.0f}s; '
          f'{time.time() - t0:.0f}s', flush=True)
    shutil.rmtree(oldsrc, ignore_errors=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--modules', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--jobs', type=int, default=8)
    ap.add_argument('--mem-gb', type=float, default=16.0)
    ap.add_argument('--timeout', type=int, default=1800)
    ap.add_argument('--accepted', action='store_true',
                    help='compile the accepted version of each module instead of the edited one, only to time it '
                         'under the same load: results go to <out>/before.jsonl, and <out>/times.json then holds '
                         'the time before and after for every module that has both')
    ap.add_argument('--paired', type=int, default=0,
                    help='time this many randomly chosen good modules both ways, accepted and edited version back to '
                         'back in the same job, and write <out>/times.json from those pairs. Use this, not '
                         '--accepted, whenever the machine was not equally busy during the batch')
    ap.add_argument('--sample', type=int, default=0,
                    help='with --accepted: time only this many modules, chosen at random among those that compiled')
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--recheck', action='store_true',
                    help='compile nothing: run the equivalence check again on the modules already compiled in '
                         '<out>/new (after the check itself changed) and rewrite results.jsonl')
    a = ap.parse_args()
    os.environ['GRH_SLOTS'] = str(a.jobs)
    from compile_one import compile_module          # after GRH_SLOTS is set

    out = os.path.abspath(a.out)
    new_dir = os.path.join(out, 'new')
    os.makedirs(new_dir, exist_ok=True)
    results_path = os.path.join(out, 'results.jsonl')

    def load(path):
        d = {}
        if os.path.exists(path):
            with open(path) as fh:
                for line in fh:
                    try:
                        r = json.loads(line)
                        d[r['module']] = r
                    except ValueError:
                        pass
        return d

    done = load(results_path)
    if a.paired:
        time_paired(a, out, done, load, compile_module)
        return
    if a.accepted:
        time_accepted(a, out, done, load, compile_module)
        return
    with open(a.modules) as fh:
        modules = [l.strip() for l in fh if l.strip()]
    todo = [m for m in modules if m not in done]
    lock = threading.Lock()
    t0 = time.time()
    counter = [0, 0]                                 # finished, good

    def checked(m, rec):
        """Run the equivalence check on a compiled module and put its outcome into the record."""
        res, old, new = IFACE.check_module(m, new_dir)
        rec.update({'compatible': res['compatible'], 'breaking': res['breaking'][:5],
                    'added': [n for n in res['added'] if not IFACE.AUX.search(n)][:5],
                    'aux_to_check': len(res['aux_to_check']), 'strict': res.get('strict'),
                    'signature_changed': res.get('signature_changed', [])[:5],
                    'ext_changed': res.get('ext_changed'), 'ns_added': res.get('ns_added'),
                    'ns_removed': res.get('ns_removed')})
        return rec

    if a.recheck:
        again = [m for m in modules if done.get(m, {}).get('ok')]
        print(f'{len(modules)} modules, {len(again)} compiled; checking them again, {a.jobs} at a time', flush=True)

        def recheck(m):
            try:
                rec = checked(m, dict(done[m]))
            except Exception as e:                   # noqa
                rec = dict(done[m]); rec.update({'compatible': False, 'breaking': [f'exception: {e}']})
            with lock:
                done[m] = rec
                counter[0] += 1
                if counter[0] % 2000 == 0:
                    print(f'{counter[0]}/{len(again)} checked, {time.time() - t0:.0f}s', flush=True)

        with ThreadPoolExecutor(max_workers=a.jobs) as pool:
            list(pool.map(recheck, again))
        tmp = results_path + '.tmp'
        with open(tmp, 'w') as fh:
            for m, rec in done.items():
                fh.write(json.dumps(rec) + '\n')
        os.replace(tmp, results_path)
        todo = []
    else:
        print(f'{len(modules)} modules, {len(done)} already done, {len(todo)} to compile, {a.jobs} at a time', flush=True)

    def work(m):
        try:
            r = compile_module(m, new_dir, overlays=[], mem_gb=a.mem_gb, timeout=a.timeout, quiet=True)
            rec = {'module': m, 'ok': r['ok'], 'time_s': r.get('time_s'), 'cpu_s': r.get('cpu_s'),
                   'wall_s': r.get('wall_s'), 'max_rss_mb': r.get('max_rss_mb'), 'sorry': r.get('mentions_sorry')}
            if r['ok']:
                checked(m, rec)
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
    why = {'did not compile': sum(1 for m in modules if m in done and not done[m].get('ok')),
           'statement or signature differs': sum(1 for m in modules if done.get(m, {}).get('ok') and done[m].get('breaking')),
           'registers different things': sum(1 for m in modules if done.get(m, {}).get('ok')
                                              and (done[m].get('ext_changed') or done[m].get('ns_removed'))),
           'not attempted': sum(1 for m in modules if m not in done)}
    print(f'finished: {len(good)} good of {len(modules)}; not good: {why}; {time.time() - t0:.0f}s', flush=True)


if __name__ == '__main__':
    main()
