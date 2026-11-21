#!/usr/bin/env python3
"""Our changes to the proof, stored as differences from the unmodified archive.

  tools/patches.py export    write patches/ from the proof repository (proof/, tag `upstream` .. HEAD)
  tools/patches.py apply     apply patches/ to a freshly extracted archive in proof/ and commit
  tools/patches.py status    show how far proof/ is from the archive and whether patches/ is current

The archive itself is not stored in this repository. `proof/` is a separate, local git repository
whose first commit is the unmodified archive. What this repository keeps is:

  patches/base.json          sha256 of the archive and the git tree hash of its extracted contents
  patches/deleted-paths.txt  files removed, one path per line (no content)
  patches/changes.diff       changed and added files, as a unified diff with no context lines

So the archive plus `patches/` reproduces our version exactly.
"""
import argparse, json, os, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C

ARCHIVE_SHA256 = '9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc'
BASE = os.path.join(C.PATCHES, 'base.json')
DELETED = os.path.join(C.PATCHES, 'deleted-paths.txt')
CHANGES = os.path.join(C.PATCHES, 'changes.diff')


def git(*args, check=True, binary=False):
    p = subprocess.run(['git', '-C', C.PROOF] + list(args), stdout=subprocess.PIPE, check=check)
    return p.stdout if binary else p.stdout.decode()


def compute():
    tree = git('rev-parse', f'{C.UPSTREAM_TAG}^{{tree}}').strip()
    deleted = git('diff', '--name-only', '--no-renames', '--diff-filter=D', C.UPSTREAM_TAG, 'HEAD')
    changes = git('diff', '--no-renames', '--diff-filter=AM', '-U0', '--no-color', '--binary', '--full-index',
                  C.UPSTREAM_TAG, 'HEAD', binary=True)
    base = json.dumps({'archive_sha256': ARCHIVE_SHA256, 'upstream_tree': tree}, indent=1) + '\n'
    return base, deleted, changes


def export():
    os.makedirs(C.PATCHES, exist_ok=True)
    base, deleted, changes = compute()
    with open(BASE, 'w') as fh:
        fh.write(base)
    with open(DELETED, 'w', encoding='utf-8') as fh:
        fh.write(deleted)
    with open(CHANGES, 'wb') as fh:
        fh.write(changes)
    n_del = len([l for l in deleted.splitlines() if l])
    n_chg = changes.count(b'\ndiff --git ') + (1 if changes.startswith(b'diff --git ') else 0)
    print(f'patches written: {n_del} deleted paths, {n_chg} changed or added files, {len(changes)} bytes of diff')


def is_current():
    try:
        base, deleted, changes = compute()
        return (open(BASE).read() == base and open(DELETED, encoding='utf-8').read() == deleted
                and open(CHANGES, 'rb').read() == changes)
    except (OSError, subprocess.CalledProcessError):
        return False


def apply():
    want = json.load(open(BASE))
    tree = git('rev-parse', f'{C.UPSTREAM_TAG}^{{tree}}').strip()
    if tree != want['upstream_tree']:
        sys.exit(f'proof/ does not start from the expected archive: tree {tree}, expected {want["upstream_tree"]}')
    if git('status', '--porcelain').strip():
        sys.exit('proof/ has uncommitted changes; refusing to apply on top of them')
    if git('rev-parse', 'HEAD').strip() != git('rev-parse', f'{C.UPSTREAM_TAG}^{{commit}}').strip():
        sys.exit('proof/ is not at the unmodified archive; apply only onto a fresh extraction')
    deleted = [l for l in open(DELETED, encoding='utf-8').read().splitlines() if l]
    for i in range(0, len(deleted), 2000):
        git('rm', '-q', '--', *deleted[i:i + 2000])
    if os.path.getsize(CHANGES) > 0:
        git('apply', '--index', '--unidiff-zero', '--whitespace=nowarn', CHANGES)
    if git('status', '--porcelain').strip():
        git('commit', '-q', '-m', 'Apply grh patches')
        print(f'applied: {len(deleted)} deleted paths and the recorded changes')
    else:
        print('no patches to apply; proof/ is the unmodified archive')


def status():
    ahead = git('rev-list', '--count', f'{C.UPSTREAM_TAG}..HEAD').strip()
    stat = git('diff', '--shortstat', '--no-renames', C.UPSTREAM_TAG, 'HEAD').strip() or 'no differences'
    dirty = bool(git('status', '--porcelain').strip())
    print(f'proof/: {ahead} commits after the archive; {stat}; uncommitted changes: {"yes" if dirty else "no"}')
    print('patches/ is ' + ('current' if is_current() else 'OUT OF DATE (run: tools/patches.py export)'))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('command', choices=['export', 'apply', 'status', 'check'])
    a = ap.parse_args()
    if a.command == 'export':
        export()
    elif a.command == 'apply':
        apply()
    elif a.command == 'status':
        status()
    else:
        sys.exit(0 if is_current() else 1)


if __name__ == '__main__':
    main()
