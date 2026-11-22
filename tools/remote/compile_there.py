#!/usr/bin/env python3
"""Compile edited files on a rented machine and bring the results back for the local judge.

  tools/remote/compile_there.py Module.A [Module.B ...] [--out build/pre]

For each module: copy its source file to the machine, run tools/try_change.py there (which compiles
the new version, and the accepted version once for timing), and copy the compiled module back to
<out>/new/. The times go to <out>/times.json. Then judge locally without compiling:

  tools/judge.py --only Module.A,Module.B --precompiled build/pre

The machine is named in grh.local.json: {"remote": {"host": "root@1.2.3.4", "port": 12345,
"path": "/root/grh"}}. It must have been set up with tools/remote/bootstrap.sh and hold the same
accepted state (compiled-overlay/ and data/overlay/ copied over).
"""
import argparse, json, os, re, subprocess, sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import common as C


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('modules', nargs='+')
    ap.add_argument('--out', default=os.path.join(C.ROOT, 'build', 'pre'))
    a = ap.parse_args()
    remote = (C.load_json(os.path.join(C.ROOT, 'grh.local.json'), {}) or {}).get('remote')
    if not remote:
        sys.exit('no "remote" entry in grh.local.json')
    host, port, rpath = remote['host'], str(remote['port']), remote.get('path', '/root/grh')
    ssh = ['ssh', '-p', port, '-o', 'BatchMode=yes', '-o', 'ConnectTimeout=20', host]
    rsync = ['rsync', '-az', '-e', f'ssh -p {port} -o BatchMode=yes']
    out = os.path.abspath(a.out)
    os.makedirs(os.path.join(out, 'new'), exist_ok=True)
    times_path = os.path.join(out, 'times.json')
    times = C.load_json(times_path, {}) or {}
    ok_all = True
    for m in a.modules:
        rel = m.replace('.', '/')
        src = C.module_path(m)
        subprocess.run(rsync + [src, f'{host}:{rpath}/proof/src/{rel}.lean'], check=True,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        # GRH_SLOTS well above what a batch running there uses, so this check does not wait behind it
        cmd = (f'cd {rpath} && export PATH=$HOME/.elan/bin:$PATH GRH_NO_SANDBOX=1 GRH_SLOTS=160 && '
               f'python3 tools/try_change.py {m}')
        p = subprocess.run(ssh + [cmd], stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        text = p.stdout.decode('utf-8', 'replace')
        print(f'--- {m}')
        print(text.strip())
        mm = re.search(r'compile time ([0-9.?]+)s -> ([0-9.]+)s', text)
        if 'DOES NOT COMPILE' in text or not mm:
            ok_all = False
            continue
        times[m] = {'before': None if mm.group(1) == '?' else float(mm.group(1)), 'after': float(mm.group(2))}
        for ext in ('.olean', '.ilean'):
            dst = C.module_path(m, os.path.join(out, 'new'), ext)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            subprocess.run(rsync + [f'{host}:{rpath}/build/try/{m}/new/{rel}{ext}', dst], check=True,
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        json.dump(times, open(times_path, 'w'), indent=1)
    sys.exit(0 if ok_all else 1)


if __name__ == '__main__':
    main()
