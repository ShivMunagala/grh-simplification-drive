#!/usr/bin/env python3
"""Bring a rented machine up to the accepted state on this machine.

  tools/remote/sync_there.py [--host root@1.2.3.4 --port 12345] [--path /root/grh]

Copies the compiled modules and table rows of every recorded change (compiled-overlay/,
data/overlay/) and the source files those changes touched, commits the source files in the
machine's own proof repository, and points its accepted state at that commit. After this, a file
compiled there is compiled against exactly what the judge here compares with.

Without --host/--port the machine named under "remote" in grh.local.json is used.
"""
import argparse, json, os, subprocess, sys, tempfile

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import common as C


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--host', default=None)
    ap.add_argument('--port', default=None)
    ap.add_argument('--path', default=None)
    a = ap.parse_args()
    remote = (C.load_json(os.path.join(C.ROOT, 'grh.local.json'), {}) or {}).get('remote') or {}
    host = a.host or remote.get('host')
    port = str(a.port or remote.get('port') or '')
    rpath = a.path or remote.get('path', '/root/grh')
    if not host or not port:
        sys.exit('no machine given: use --host/--port or a "remote" entry in grh.local.json')
    state = C.accepted_state()
    if not state:
        sys.exit('nothing has been recorded yet; the machine is already at the accepted state')
    ssh = ['ssh', '-p', port, '-o', 'BatchMode=yes', '-o', 'ConnectTimeout=20', host]
    rsync = ['rsync', '-az', '-e', f'ssh -p {port} -o BatchMode=yes']

    def run(cmd, **kw):
        return subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, **kw)

    # --checksum: files the machine compiled itself and already holds are recognised by content, not by date
    run(rsync + ['--delete', '--checksum', os.path.join(C.ROOT, 'compiled-overlay') + '/',
                 f'{host}:{rpath}/compiled-overlay/'], check=True)
    # state.json names a commit of the proof repository here, which the machine does not have. It is sent
    # under another name and put in place at the end with the machine's own commit, in one step, so that
    # jobs running there never see a state that names a commit they cannot read.
    run(rsync + ['--exclude', 'state.json', '--exclude', 'state.json.incoming', C.DATA_OVERLAY + '/',
                 f'{host}:{rpath}/data/overlay/'], check=True)
    run(rsync + [os.path.join(C.DATA_OVERLAY, 'state.json'), f'{host}:{rpath}/data/overlay/state.json.incoming'],
        check=True)
    # source of the modules recorded changes touched, as committed here
    rels = ['src/' + m.replace('.', '/') + '.lean' for m in state['modules']]
    with tempfile.TemporaryDirectory() as tmp:
        # one git process for all files
        req = ''.join(f"{state['proof_commit']}:{rel}\n" for rel in rels).encode()
        blob = subprocess.run(['git', '-C', C.PROOF, 'cat-file', '--batch'], input=req, stdout=subprocess.PIPE,
                              check=True).stdout
        pos = 0
        for rel in rels:
            nl = blob.index(b'\n', pos)
            header = blob[pos:nl].split()
            if len(header) < 3 or header[1] != b'blob':
                sys.exit(f'{rel} is not in the accepted commit')
            size = int(header[2])
            dst = os.path.join(tmp, rel)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            with open(dst, 'wb') as fh:
                fh.write(blob[nl + 1:nl + 1 + size])
            pos = nl + 1 + size + 1
        listing = os.path.join(tmp, 'files.txt')
        with open(listing, 'w') as fh:
            fh.write('\n'.join(rels) + '\n')
        # --checksum: a file that already has the accepted text there is left alone
        run(rsync + ['--checksum', os.path.join(tmp, 'src'), f'{host}:{rpath}/proof/'], check=True)
        run(rsync + [listing, f'{host}:{rpath}/build/sync_files.txt'], check=True)
    script = f'''
cd {rpath} || exit 1
git -C proof add --pathspec-from-file={rpath}/build/sync_files.txt
git -C proof -c user.name=grh -c user.email=grh@localhost commit -q -m "accepted state" --only --pathspec-from-file={rpath}/build/sync_files.txt 2>/dev/null
H=$(git -C proof rev-parse HEAD)
python3 - "$H" <<PY
import json, os, sys
p = "data/overlay/state.json"
s = json.load(open(p + ".incoming"))
s["proof_commit"] = sys.argv[1]
json.dump(s, open(p + ".incoming", "w"), indent=1)
os.replace(p + ".incoming", p)
print("machine is at the accepted state:", len(s["modules"]), "changed modules; its commit", sys.argv[1][:10])
PY
'''
    p = subprocess.run(ssh + ['bash -s'], input=script.encode(), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out = p.stdout.decode().strip().splitlines()
    print(out[-1] if out else p.stderr.decode()[-300:])
    sys.exit(p.returncode)


if __name__ == '__main__':
    main()
