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
import argparse, json, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C


def compile_module(module, out, src=C.SRC, overlays=(), threads=1, mem_gb=8.0, timeout=3600, quiet=False):
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
    with open(setup, 'w') as fh:
        # imports are resolved through LEAN_PATH, so no pre-resolved artifacts are listed
        json.dump({'name': module, 'isModule': False, 'importArts': {}, 'dynlibs': [], 'plugins': [],
                   'options': {}}, fh)
    log = olean + '.log'
    overlays = [os.path.abspath(o) for o in overlays]
    lean_path = ':'.join(overlays + [C.COMPILED] + C.package_libs())
    opts = list(C.LEAN_OPTS)
    if module.startswith(C.FIELDS_PREFIXES):
        opts += C.FIELDS_OPTS
    stats = olean + '.stats.json'
    if os.path.exists(stats):
        os.remove(stats)
    tools = os.path.dirname(os.path.abspath(__file__))
    cmd = ['/usr/bin/python3', '-I', os.path.join(tools, 'timed_exec.py'), stats, '--',
           C.LEAN, f'-j{threads}', f'--setup={setup}', '-o', olean, '-i', ilean] + opts + [source]
    ro = [C.TOOLCHAIN, C.PACKAGES, C.COMPILED, src, tools] + overlays
    boxed = C.sandbox(cmd, ro=ro, rw=[out], env={'LEAN_PATH': lean_path, 'LEAN_ABORT_ON_PANIC': '1'})
    with open(log, 'w') as lf:
        rc, _, wall, _ = C.run_timed(boxed, mem_gb=mem_gb, stdout=lf, stderr=lf, timeout=timeout)
    st = C.load_json(stats, {}) or {}
    cpu = st.get('user_s', 0.0) + st.get('sys_s', 0.0)
    rss = st.get('max_rss_mb', 0.0)
    ok = rc == 0 and os.path.exists(olean)
    messages = ''
    try:
        with open(log, errors='replace') as lf:
            messages = lf.read()
    except OSError:
        pass
    has_error = ': error' in messages
    has_sorry = "declaration uses 'sorry'" in messages or 'sorry' in messages and 'warning' in messages
    res = {'module': module, 'ok': ok and not has_error, 'rc': rc, 'cpu_s': round(cpu, 2), 'wall_s': round(wall, 2),
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
