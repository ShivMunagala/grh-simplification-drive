#!/usr/bin/env python3
"""Compile one source file against the compiled base, in a sandbox, and report time and memory.

  tools/compile_one.py Development.Some.Module --out build/x [--src proof/src] [--overlay build/y ...]

The file's imports are taken from, in order: the --overlay directories (modules recompiled for the
current change), the compiled base (`compiled/lib/lean`), then Mathlib and its dependencies.
Nothing else is rebuilt. The result goes to <out>/<Module/Path>.olean and .ilean.

The archive's source is untrusted and compiling it runs code, so the compiler runs under bubblewrap
with no network and a read-only filesystem, and under a memory cap so that a file that is too big
for this machine fails cleanly instead of making it swap.
"""
import argparse, fcntl, json, os, re, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C


SECOND_SLOT_MIN_FREE_GB = 6.5
PROFILE_LINE = re.compile(r'^\t(.+?) ([0-9.]+)(ms|s)$', re.M)
NOT_WORK = {'import', 'initialization'}


def work_seconds(log_text):
    """Time Lean spent elaborating and checking the file, from its own cumulative timing report.

    Loading the imports is left out: on a machine short of memory it dominates and swings widely,
    and it says nothing about the file being compiled. Returns None if the report is missing."""
    k = log_text.rfind('cumulative profiling times:')
    if k < 0:
        return None
    total, seen = 0.0, False
    for name, value, unit in PROFILE_LINE.findall(log_text[k:]):
        if name.strip() in NOT_WORK:
            continue
        total += float(value) * (0.001 if unit == 'ms' else 1.0)
        seen = True
    return total if seen else None


def mem_available_gb():
    try:
        with open('/proc/meminfo') as fh:
            for line in fh:
                if line.startswith('MemAvailable:'):
                    return int(line.split()[1]) / (1024.0 * 1024.0)
    except OSError:
        pass
    return 0.0


def acquire_slot():
    """Wait for a compile slot. Memory is the limit on this machine: one compile at a time,
    and a second one only while plenty of memory is free."""
    os.makedirs(os.path.dirname(C.LOCK), exist_ok=True)
    while True:
        for i, path in enumerate((C.LOCK, C.LOCK + '2')):
            if i == 1 and mem_available_gb() < SECOND_SLOT_MIN_FREE_GB:
                continue
            fh = open(path, 'w')
            try:
                fcntl.flock(fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
                return fh
            except BlockingIOError:
                fh.close()
        time.sleep(2)


def compile_module(module, out, src=C.SRC, overlays=(), threads=1, mem_gb=8.0, timeout=3600, quiet=False,
                   use_accepted=True):
    out = os.path.abspath(out)
    src = os.path.abspath(src)
    source = C.module_path(module, src)
    if not os.path.exists(source):
        return {'module': module, 'ok': False, 'error': f'no source file {source}'}
    olean = C.module_path(module, out, '.olean')
    ilean = C.module_path(module, out, '.ilean')
    os.makedirs(os.path.dirname(olean), exist_ok=True)
    for p in (olean, ilean):
        if os.path.exists(p):
            os.remove(p)
    setup = olean + '.setup.json'
    log = olean + '.log'
    overlays = [os.path.abspath(o) for o in overlays]
    if use_accepted and os.path.isdir(C.OVERLAY) and C.OVERLAY not in overlays:
        overlays.append(C.OVERLAY)          # modules changed by earlier accepted changes
    # Overlay modules are named one by one in the setup file. They cannot simply go first on the
    # search path: Lean resolves a whole top-level folder (say `Development`) to the first path
    # entry that has it, so a partial overlay would hide every other module under that folder.
    arts = {}
    for o in overlays:
        for dp, dn, fn in os.walk(o):
            for f in fn:
                if f.endswith('.olean'):
                    p = os.path.join(dp, f)
                    mod = os.path.relpath(p, o)[:-6].replace(os.sep, '.')
                    if mod != module and mod not in arts:
                        arts[mod] = [[p]]
    with open(setup, 'w') as fh:
        json.dump({'name': module, 'isModule': False, 'importArts': arts, 'dynlibs': [], 'plugins': [],
                   'options': {}}, fh)
    lean_path = ':'.join([C.COMPILED] + C.package_libs())
    opts = list(C.LEAN_OPTS)
    if module.startswith(C.FIELDS_PREFIXES):
        opts += C.FIELDS_OPTS
    stats = olean + '.stats.json'
    if os.path.exists(stats):
        os.remove(stats)
    tools = os.path.dirname(os.path.abspath(__file__))
    # Lean's own per-phase timing, printed once at the end; the threshold keeps per-declaration lines out
    opts += ['-Dprofiler=true', '-Dprofiler.threshold=1000000000']
    cmd = ['/usr/bin/python3', '-I', os.path.join(tools, 'timed_exec.py'), stats, '--',
           C.LEAN, f'-j{threads}', f'--setup={setup}', '-o', olean, '-i', ilean] + opts + [source]
    ro = [C.TOOLCHAIN, C.PACKAGES, C.COMPILED, src, tools] + overlays
    boxed = C.sandbox(cmd, ro=ro, rw=[out], env={'LEAN_PATH': lean_path, 'LEAN_ABORT_ON_PANIC': '1'})
    with acquire_slot() as _slot, open(log, 'w') as lf:
        rc, _, wall, _ = C.run_timed(boxed, mem_gb=mem_gb, stdout=lf, stderr=lf, timeout=timeout)
    st = C.load_json(stats, {}) or {}
    cpu = st.get('user_s', 0.0)             # user time only: system time swings with memory pressure
    rss = st.get('max_rss_mb', 0.0)
    ok = rc == 0 and os.path.exists(olean)
    messages = ''
    try:
        with open(log, errors='replace') as lf:
            messages = lf.read()
    except OSError:
        pass
    work = work_seconds(messages)
    time_s = work if work is not None else cpu
    k = messages.find('cumulative profiling times:')
    if k >= 0:
        messages = messages[:k]                 # keep the timing block out of error reports
    has_error = ': error' in messages
    has_sorry = "declaration uses 'sorry'" in messages or 'sorry' in messages and 'warning' in messages
    res = {'module': module, 'ok': ok and not has_error, 'rc': rc, 'time_s': round(time_s, 2),
           'cpu_s': round(cpu, 2), 'wall_s': round(wall, 2),
           'max_rss_mb': round(rss), 'olean': olean if ok else None, 'ilean': ilean if ok else None,
           'log': log, 'has_error': has_error, 'mentions_sorry': bool(has_sorry),
           'messages_tail': messages[-1500:] if (not ok or has_error) else ''}
    if not quiet:
        print(json.dumps(res, indent=1))
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('module')
    ap.add_argument('--out', required=True)
    ap.add_argument('--src', default=C.SRC)
    ap.add_argument('--overlay', action='append', default=[])
    ap.add_argument('--threads', type=int, default=1)
    ap.add_argument('--mem-gb', type=float, default=8.0)
    ap.add_argument('--timeout', type=int, default=3600)
    a = ap.parse_args()
    r = compile_module(a.module, a.out, a.src, a.overlay, a.threads, a.mem_gb, a.timeout)
    sys.exit(0 if r['ok'] else 1)


if __name__ == '__main__':
    main()
