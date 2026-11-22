#!/usr/bin/env python3
"""Our changes to the proof, stored as differences from the unmodified archive.

  tools/patches.py export    write patches/ from the proof repository (proof/, tag `upstream` .. HEAD)
  tools/patches.py apply     apply patches/ to a freshly extracted archive in proof/ and commit
  tools/patches.py status    show how far proof/ is from the archive and whether patches/ is current

The archive itself is not stored in this repository, and neither is any line of it. `proof/` is a
separate, local git repository whose first commit is the unmodified archive. What this repository
keeps is:

  patches/base.json             sha256 of the archive and the git tree hash of its extracted contents
  patches/deleted-paths.txt     files removed, one path per line (no content)
  patches/aliased-wrappers.tsv  files rewritten by tools/alias_wrappers.py: module, wrapper, original.
                                Names only; the rewrite is mechanical and is redone from this list.
  patches/changes.patch         every other changed or added file, as line ranges to replace and the
                                new lines. The replaced lines themselves are not stored: each file is
                                identified by the sha256 of its archive version, so the ranges are exact.

Format of changes.patch:

  == <path> <sha256 of the archive's file, or `new`> <sha256 of our file>
  @@ <first line>,<number of lines>     lines of the archive's file that are replaced (0: insert before <first line>)
  +<new line>                           what replaces them, one `+` line per line

So the archive plus `patches/` reproduces our version exactly, and the repository carries only text we wrote.
"""
import argparse, difflib, hashlib, json, os, re, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C
import alias_wrappers as ALIAS

ARCHIVE_SHA256 = '9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc'
BASE = os.path.join(C.PATCHES, 'base.json')
DELETED = os.path.join(C.PATCHES, 'deleted-paths.txt')
ALIASED = os.path.join(C.PATCHES, 'aliased-wrappers.tsv')
CHANGES = os.path.join(C.PATCHES, 'changes.patch')
OLD_CHANGES = os.path.join(C.PATCHES, 'changes.diff')        # earlier format, which quoted the replaced lines
ALIAS_LINE = re.compile(r'^alias (?:_root_\.)?(\S+) := (\S+)\n\Z', re.M)


def git(*args, check=True, binary=False, stdin=None):
    p = subprocess.run(['git', '-C', C.PROOF] + list(args), stdout=subprocess.PIPE, check=check, input=stdin)
    return p.stdout if binary else p.stdout.decode()


def texts_at(rev, paths):
    """Contents of many files at a revision of proof/, read with one git process. Missing files are left out."""
    if not paths:
        return {}
    req = ''.join(f'{rev}:{p}\n' for p in paths).encode()
    out = git('cat-file', '--batch', binary=True, stdin=req)
    res, pos = {}, 0
    for p in paths:
        nl = out.index(b'\n', pos)
        header = out[pos:nl].split()
        if len(header) < 3:                      # "<spec> missing"
            pos = nl + 1
            continue
        size = int(header[2])
        res[p] = out[nl + 1:nl + 1 + size].decode('utf-8')
        pos = nl + 1 + size + 1
    return res


def sha(text):
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


def hunks(old, new):
    """Line ranges of `old` to replace and the lines that replace them, without the replaced lines."""
    a, b = old.split('\n'), new.split('\n')
    out = []
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
        if tag != 'equal':
            out.append((i1 + 1, i2 - i1, b[j1:j2]))
    return out


def block(path, old, new):
    """One file's entry in changes.patch. old is None for a file we added."""
    lines = [f'== {path} {sha(old) if old is not None else "new"} {sha(new)}']
    for start, count, repl in hunks(old if old is not None else '', new):
        lines.append(f'@@ {start},{count}')
        lines += ['+' + l for l in repl]
    return '\n'.join(lines) + '\n'


def parse_blocks(text):
    """-> [(path, old sha or 'new', new sha, [(start, count, [lines])])]"""
    blocks = []
    for line in text.split('\n'):
        if line.startswith('== '):
            path, old_sha, new_sha = line[3:].rsplit(' ', 2)
            blocks.append((path, old_sha, new_sha, []))
        elif line.startswith('@@ '):
            start, count = line[3:].split(',')
            blocks[-1][3].append((int(start), int(count), []))
        elif line.startswith('+'):
            blocks[-1][3][-1][2].append(line[1:])
    return blocks


def patched(old, hs):
    lines = old.split('\n')
    for start, count, repl in sorted(hs, reverse=True):       # from the end, so earlier positions stay valid
        lines[start - 1:start - 1 + count] = repl
    return '\n'.join(lines)


def compute():
    tree = git('rev-parse', f'{C.UPSTREAM_TAG}^{{tree}}').strip()
    deleted = git('diff', '--name-only', '--no-renames', '--diff-filter=D', C.UPSTREAM_TAG, 'HEAD')
    modified = [p for p in git('diff', '--name-only', '--no-renames', '--diff-filter=M', C.UPSTREAM_TAG, 'HEAD')
                .splitlines() if p]
    added = [p for p in git('diff', '--name-only', '--no-renames', '--diff-filter=A', C.UPSTREAM_TAG, 'HEAD')
             .splitlines() if p]
    old = texts_at(C.UPSTREAM_TAG, modified)
    new = texts_at('HEAD', modified + added)
    # files that are exactly "the archive's wrapper, rewritten as an alias" are stored as names only
    aliased, blocks = [], []
    for p in sorted(modified):
        m = ALIAS_LINE.search(new[p]) if p.endswith('Statement.lean') else None
        if m and ALIAS.rewrite(old[p], m.group(1), m.group(2)) == new[p]:
            module = p[len('src/'):-len('.lean')].replace('/', '.')
            aliased.append(f'{module}\t{m.group(1)}\t{m.group(2)}\n')
        else:
            blocks.append(block(p, old[p], new[p]))
    for p in sorted(added):
        blocks.append(block(p, None, new[p]))
    base = json.dumps({'archive_sha256': ARCHIVE_SHA256, 'upstream_tree': tree}, indent=1) + '\n'
    return base, deleted, ''.join(sorted(aliased)), ''.join(blocks)


def export():
    os.makedirs(C.PATCHES, exist_ok=True)
    base, deleted, aliased, changes = compute()
    with open(BASE, 'w') as fh:
        fh.write(base)
    with open(DELETED, 'w', encoding='utf-8') as fh:
        fh.write(deleted)
    with open(ALIASED, 'w', encoding='utf-8') as fh:
        fh.write(aliased)
    with open(CHANGES, 'w', encoding='utf-8', newline='') as fh:
        fh.write(changes)
    if os.path.exists(OLD_CHANGES):
        os.remove(OLD_CHANGES)
    n_del = len([l for l in deleted.splitlines() if l])
    n_chg = sum(1 for l in changes.split('\n') if l.startswith('== '))
    print(f'patches written: {n_del} deleted paths, {aliased.count(chr(10))} aliased wrappers, '
          f'{n_chg} other changed or added files, {len(changes.encode("utf-8"))} bytes of replacement text')


def read(path, mode='r'):
    try:
        with open(path, mode, **({} if 'b' in mode else {'encoding': 'utf-8', 'newline': ''})) as fh:
            return fh.read()
    except OSError:
        return b'' if 'b' in mode else ''


def is_current():
    try:
        base, deleted, aliased, changes = compute()
    except subprocess.CalledProcessError:
        return False
    return (read(BASE) == base and read(DELETED) == deleted and read(ALIASED) == aliased
            and read(CHANGES) == changes)


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
    if os.path.exists(OLD_CHANGES) and not os.path.exists(CHANGES) and os.path.getsize(OLD_CHANGES) > 0:
        git('apply', '--index', '--unidiff-zero', '--whitespace=nowarn', OLD_CHANGES)      # earlier format
    n_changed = 0
    for path, old_sha, new_sha, hs in parse_blocks(read(CHANGES)):
        full = os.path.join(C.PROOF, path)
        if old_sha == 'new':
            old = ''
            os.makedirs(os.path.dirname(full), exist_ok=True)
        else:
            with open(full, encoding='utf-8', newline='') as fh:
                old = fh.read()
            if sha(old) != old_sha:
                sys.exit(f'{path} is not the archive version this patch was made for')
        new = patched(old, hs)
        if sha(new) != new_sha:
            sys.exit(f'{path}: the patched file does not have the recorded hash')
        with open(full, 'w', encoding='utf-8', newline='') as fh:
            fh.write(new)
        n_changed += 1
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
    if n_alias or n_changed:
        git('add', '-A')
    if git('status', '--porcelain').strip():
        git('commit', '-q', '-m', 'Apply grh patches')
        print(f'applied: {len(deleted)} deleted paths, {n_alias} aliased wrappers, {n_changed} other changed or added files')
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
