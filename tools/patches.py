#!/usr/bin/env python3
"""Our changes to the proof, stored as differences from the unmodified archive.

  tools/patches.py export    write patches/ from the proof repository (proof/, tag `upstream` .. HEAD)
  tools/patches.py apply     apply patches/ to a freshly extracted archive in proof/ and commit
  tools/patches.py status    show how far proof/ is from the archive and whether patches/ is current

The archive itself is not stored in this repository. `proof/` is a separate, local git repository
whose first commit is the unmodified archive. What this repository keeps is:

  patches/base.json             sha256 of the archive and the git tree hash of its extracted contents
  patches/deleted-paths.txt     files removed, one path per line (no content)
  patches/aliased-wrappers.tsv  files rewritten by tools/alias_wrappers.py: module, wrapper, original.
                                Names only; the rewrite is mechanical and is redone from this list.
  patches/changes.diff          every other changed or added file, as a unified diff with no context

So the archive plus `patches/` reproduces our version exactly, and the repository carries as little
of the archive's text as possible.
"""
import argparse, json, os, re, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C
import alias_wrappers as ALIAS

ARCHIVE_SHA256 = '9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc'
BASE = os.path.join(C.PATCHES, 'base.json')
DELETED = os.path.join(C.PATCHES, 'deleted-paths.txt')
ALIASED = os.path.join(C.PATCHES, 'aliased-wrappers.tsv')
CHANGES = os.path.join(C.PATCHES, 'changes.diff')
ALIAS_LINE = re.compile(r'^alias (?:_root_\.)?(\S+) := (\S+)\n\Z', re.M)


def git(*args, check=True, binary=False, stdin=None):
    p = subprocess.run(['git', '-C', C.PROOF] + list(args), stdout=subprocess.PIPE, check=check, input=stdin)
    return p.stdout if binary else p.stdout.decode()


def upstream_texts(paths):
    """Contents of many files at the unmodified archive, read with one git process."""
    if not paths:
        return {}
    req = ''.join(f'{C.UPSTREAM_TAG}:{p}\n' for p in paths).encode()
    out = git('cat-file', '--batch', binary=True, stdin=req)
    res, pos = {}, 0
    for p in paths:
        nl = out.index(b'\n', pos)
        header = out[pos:nl].split()
        if len(header) < 3:                      # "<spec> missing"
            pos = nl + 1
            continue
        size = int(header[2])
        res[p] = out[nl + 1:nl + 1 + size].decode('utf-8', 'replace')
        pos = nl + 1 + size + 1
    return res


def split_diff(diff):
    """Split a unified diff into {path: section bytes}."""
    parts = re.split(rb'(?m)^(?=diff --git )', diff)
    res = {}
    for part in parts:
        m = re.match(rb'diff --git a/(.+?) b/(.+?)\n', part)
        if m:
            res[m.group(2).decode('utf-8', 'replace')] = part
    return res


def compute():
    tree = git('rev-parse', f'{C.UPSTREAM_TAG}^{{tree}}').strip()
    deleted = git('diff', '--name-only', '--no-renames', '--diff-filter=D', C.UPSTREAM_TAG, 'HEAD')
    modified = [p for p in git('diff', '--name-only', '--no-renames', '--diff-filter=M', C.UPSTREAM_TAG, 'HEAD')
                .splitlines() if p]
    # files that are exactly "the archive's wrapper, rewritten as an alias" are stored as names only
    candidates = [p for p in modified if p.endswith('Statement.lean')]
    old = upstream_texts(candidates)
    aliased = []
    skip = set()
    for p in candidates:
        try:
            with open(os.path.join(C.PROOF, p), encoding='utf-8') as fh:
                new = fh.read()
        except OSError:
            continue
        m = ALIAS_LINE.search(new)
        if m and p in old and ALIAS.rewrite(old[p], m.group(1), m.group(2)) == new:
            module = p[len('src/'):-len('.lean')].replace('/', '.')
            aliased.append(f'{module}\t{m.group(1)}\t{m.group(2)}\n')
            skip.add(p)
    diff = git('diff', '--no-renames', '--diff-filter=AM', '-U0', '--no-color', '--binary', '--full-index',
               C.UPSTREAM_TAG, 'HEAD', binary=True)
    if skip:
        sections = split_diff(diff)
        diff = b''.join(sec for path, sec in sections.items() if path not in skip)
    base = json.dumps({'archive_sha256': ARCHIVE_SHA256, 'upstream_tree': tree}, indent=1) + '\n'
    return base, deleted, ''.join(sorted(aliased)), diff


def export():
    os.makedirs(C.PATCHES, exist_ok=True)
    base, deleted, aliased, changes = compute()
    with open(BASE, 'w') as fh:
        fh.write(base)
    with open(DELETED, 'w', encoding='utf-8') as fh:
        fh.write(deleted)
    with open(ALIASED, 'w', encoding='utf-8') as fh:
        fh.write(aliased)
    with open(CHANGES, 'wb') as fh:
        fh.write(changes)
    n_del = len([l for l in deleted.splitlines() if l])
    n_chg = changes.count(b'\ndiff --git ') + (1 if changes.startswith(b'diff --git ') else 0)
    print(f'patches written: {n_del} deleted paths, {aliased.count(chr(10))} aliased wrappers, '
          f'{n_chg} other changed or added files, {len(changes)} bytes of diff')


def read(path, mode='r'):
    try:
        with open(path, mode, **({} if 'b' in mode else {'encoding': 'utf-8'})) as fh:
            return fh.read()
    except OSError:
        return b'' if 'b' in mode else ''


def is_current():
    try:
        base, deleted, aliased, changes = compute()
    except subprocess.CalledProcessError:
        return False
    return (read(BASE) == base and read(DELETED) == deleted and read(ALIASED) == aliased
            and read(CHANGES, 'rb') == changes)


def apply():
    want = json.load(open(BASE))
    tree = git('rev-parse', f'{C.UPSTREAM_TAG}^{{tree}}').strip()
    if tree != want['upstream_tree']:
        sys.exit(f'proof/ does not start from the expected archive: tree {tree}, expected {want["upstream_tree"]}')
    if git('status', '--porcelain').strip():
        sys.exit('proof/ has uncommitted changes; refusing to apply on top of them')
    if git('rev-parse', 'HEAD').strip() != git('rev-parse', f'{C.UPSTREAM_TAG}^{{commit}}').strip():
        sys.exit('proof/ is not at the unmodified archive; apply only onto a fresh extraction')
    deleted = [l for l in read(DELETED).splitlines() if l]
    for i in range(0, len(deleted), 2000):
        git('rm', '-q', '--', *deleted[i:i + 2000])
    if os.path.exists(CHANGES) and os.path.getsize(CHANGES) > 0:
        git('apply', '--index', '--unidiff-zero', '--whitespace=nowarn', CHANGES)
    n_alias = 0
    for line in read(ALIASED).splitlines():
        module, wrapper, target = line.split('\t')
        p = C.module_path(module)
        with open(p, encoding='utf-8') as fh:
            new = ALIAS.rewrite(fh.read(), wrapper, target)
        if new is None:
            sys.exit(f'{module} does not have the expected wrapper shape; cannot rebuild our version')
        with open(p, 'w', encoding='utf-8') as fh:
            fh.write(new)
        n_alias += 1
    if n_alias:
        git('add', '-A')
    if git('status', '--porcelain').strip():
        git('commit', '-q', '-m', 'Apply grh patches')
        print(f'applied: {len(deleted)} deleted paths, {n_alias} aliased wrappers and the recorded changes')
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
