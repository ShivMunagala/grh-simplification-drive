#!/usr/bin/env python3
"""Stream the compiled archive and write per-declaration tables, without unpacking it.

  tools/dump_stream.py --archive upstream-dl/compiled/oleans.tar.zst --out data/base [--limit N]

Reads `oleans.tar.zst` member by member:
  * `.ilean` files are JSON; their declaration ranges go to  <out>/decls.tsv.zst
  * `.olean` files are written to a scratch directory, handed to `moddump` (run inside a
    bubblewrap sandbox with no network), and removed again; its records go to <out>/consts.tsv.zst

Only a few hundred megabytes of scratch space are in use at any time. The compiled files come from
compiling untrusted code, so nothing here executes them; `moddump` only maps them and walks the data.

If `moddump` dies on a module (for example out of memory on a very large proof), the module is
retried once without size computation and the run continues.
"""
import argparse, json, os, re, shutil, subprocess, sys, tarfile, time

SAFE = re.compile(r'^(?:\./)?\.lake/build/lib/lean/((?:[^/\x00]+/)*[^/\x00]+)\.(olean|ilean)$')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--archive', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--moddump', default=os.path.join(os.path.dirname(__file__), 'moddump/.lake/build/bin/moddump'))
    ap.add_argument('--scratch', default=None)
    ap.add_argument('--limit', type=int, default=0, help='stop after this many modules (0 = all)')
    ap.add_argument('--sizes', choices=['both', 'raw', 'none'], default='raw')
    ap.add_argument('--mem-gb', type=float, default=5.0, help='address-space cap for moddump')
    ap.add_argument('--keep', default=None,
                    help='also keep every .olean under this directory (about 99 GB before filesystem compression)')
    ap.add_argument('--min-free-gb', type=float, default=60.0, help='stop if free disk space falls below this')
    a = ap.parse_args()
    if a.keep:
        a.keep = os.path.abspath(a.keep)
        os.makedirs(a.keep, exist_ok=True)

    os.makedirs(a.out, exist_ok=True)
    scratch = os.path.abspath(a.scratch or os.path.join(a.out, 'scratch'))
    shutil.rmtree(scratch, ignore_errors=True)
    os.makedirs(scratch)
    extra = {'both': [], 'raw': ['--noshared'], 'none': ['--nosize']}[a.sizes]

    zin = subprocess.Popen(['zstd', '-dc', '--long=31', a.archive], stdout=subprocess.PIPE)
    consts_z = subprocess.Popen(['zstd', '-q', '-3', '-T2', '-f', '-o', os.path.join(a.out, 'consts.tsv.zst')],
                                stdin=subprocess.PIPE)
    decls_z = subprocess.Popen(['zstd', '-q', '-3', '-f', '-o', os.path.join(a.out, 'decls.tsv.zst')],
                               stdin=subprocess.PIPE)
    log = open(os.path.join(a.out, 'dump.log'), 'w')

    def limit():
        import resource
        cap = int(a.mem_gb * (1 << 30))
        resource.setrlimit(resource.RLIMIT_AS, (cap, cap))

    def spawn(extra_args):
        tooldir = os.path.dirname(os.path.abspath(a.moddump))
        cmd = ['bwrap', '--unshare-all', '--die-with-parent',
               '--ro-bind', '/', '/', '--dev', '/dev', '--proc', '/proc',
               '--tmpfs', '/home', '--tmpfs', '/tmp',
               '--ro-bind', tooldir, tooldir,
               '--bind', scratch, scratch,
               '--', os.path.abspath(a.moddump), '--delete'] + extra_args
        return subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=consts_z.stdin, preexec_fn=limit)

    dumper = spawn(extra)
    pending = []          # (module, path) handed to the dumper and not yet seen removed
    failed = []
    t0 = time.time()
    n_olean = n_ilean = 0
    bytes_olean = 0

    def drain(max_left):
        """Wait until at most `max_left` handed-over files remain; handle a dead dumper."""
        nonlocal dumper, pending
        while True:
            pending = [(m, p) for (m, p) in pending if os.path.exists(p)]
            if len(pending) <= max_left:
                return
            if dumper.poll() is not None:
                # the dumper died on the first file still present
                bad_m, bad_p = pending[0]
                rest = pending[1:]
                log.write(f'DUMPER_DIED rc={dumper.returncode} module={bad_m}\n'); log.flush()
                # the dead process may have left a half-written line; terminate it and mark the module
                consts_z.stdin.write(f'\nX\t{bad_m}\tdumper died rc={dumper.returncode}\n'.encode())
                consts_z.stdin.flush()
                retry = spawn(['--nosize'])
                retry.stdin.write(f'{bad_m}\t{bad_p}\n'.encode()); retry.stdin.close()
                rc = retry.wait()
                if os.path.exists(bad_p):
                    os.remove(bad_p)
                failed.append((bad_m, 'nosize-ok' if rc == 0 else f'failed rc={rc}'))
                log.write(f'RETRY module={bad_m} rc={rc}\n'); log.flush()
                dumper = spawn(extra)
                for m, p in rest:
                    dumper.stdin.write(f'{m}\t{p}\n'.encode())
                dumper.stdin.flush()
                pending = rest
                continue
            time.sleep(0.02)

    tar = tarfile.open(fileobj=zin.stdout, mode='r|')
    for member in tar:
        if member.isdir():
            continue
        mm = SAFE.match(member.name)
        if not member.isreg() or not mm or '..' in member.name.split('/'):
            log.write(f'SKIP {member.name!r} type={member.type!r}\n')
            continue
        module = mm.group(1).replace('/', '.')
        f = tar.extractfile(member)
        if mm.group(2) == 'ilean':
            n_ilean += 1
            try:
                d = json.loads(f.read())
                for name, r in (d.get('decls') or {}).items():
                    decls_z.stdin.write(f'{module}\t{r[0]}\t{r[1]}\t{r[2]}\t{r[3]}\t{name}\n'.encode())
            except Exception as e:  # noqa
                log.write(f'ILEAN_ERROR {module} {e}\n')
            continue
        n_olean += 1
        bytes_olean += member.size
        path = os.path.join(scratch, f'{n_olean}.olean')
        if a.keep:
            # keep the compiled file under --keep and hand the reader a hard link to it
            kept = os.path.join(a.keep, mm.group(1) + '.olean')
            os.makedirs(os.path.dirname(kept), exist_ok=True)
            with open(kept, 'wb') as o:
                shutil.copyfileobj(f, o, 1 << 20)
            os.chmod(kept, 0o444)
            os.link(kept, path)
        else:
            with open(path, 'wb') as o:
                shutil.copyfileobj(f, o, 1 << 20)
        if a.min_free_gb and n_olean % 500 == 0:
            st = os.statvfs(scratch)
            if st.f_bavail * st.f_frsize < a.min_free_gb * (1 << 30):
                log.write(f'STOP low disk space at module {n_olean}\n'); log.flush()
                print('stopping: low disk space', file=sys.stderr)
                break
        try:
            dumper.stdin.write(f'{module}\t{path}\n'.encode())
            dumper.stdin.flush()
        except BrokenPipeError:
            pass
        pending.append((module, path))
        if len(pending) >= 64:
            drain(16)
        if n_olean % 5000 == 0:
            el = time.time() - t0
            log.write(f'PROGRESS modules={n_olean} olean_gb={bytes_olean / 1e9:.1f} elapsed={el:.0f}s\n'); log.flush()
        if a.limit and n_olean >= a.limit:
            break

    drain(0)
    try:
        dumper.stdin.close()
    except Exception:
        pass
    dumper.wait()
    zin.kill()
    consts_z.stdin.close(); consts_z.wait()
    decls_z.stdin.close(); decls_z.wait()
    el = time.time() - t0
    summary = {'modules': n_olean, 'ileans': n_ilean, 'olean_bytes': bytes_olean, 'seconds': round(el),
               'failed': failed, 'sizes': a.sizes}
    json.dump(summary, open(os.path.join(a.out, 'dump_summary.json'), 'w'), indent=1)
    log.write(f'DONE {json.dumps(summary)}\n'); log.close()
    shutil.rmtree(scratch, ignore_errors=True)
    print(json.dumps(summary))


if __name__ == '__main__':
    main()
