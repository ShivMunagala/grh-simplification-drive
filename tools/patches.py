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
  patches/changes.patch         every other changed or added file, as character spans to replace and
                                the text that replaces them. Neither the replaced text nor the unchanged
                                part of an edited line is stored: each file is identified by the sha256
                                of its archive version, so the spans are exact. Where the replacing text
                                repeats a run of the archive's file (a line that a rewrite kept or moved),
                                the run is stored as a position and a length, not as text.

Format of changes.patch:

  == <path> <sha256 of the archive's file, or `new`> <sha256 of our file>
  @@ <start> <old length> <new length>   span of the archive's file (in characters) that is replaced
  <new text, exactly <new length> characters, then a newline>
  @% <start> <old length> <pieces>       the same, with the replacing text given in pieces, each either
  + <length>                               text we wrote: <length> characters on the next line, or
  <text>
  = <position> <length>                    a run of the archive's own file, by position and length

Every run of MIN_COPY or more characters that the replacing text shares with the archive's version of the
same file is given the second way. So the archive plus `patches/` reproduces our version exactly, and the
repository carries only text we wrote.
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
MIN_COPY = 24            # a shared run this long is stored as a reference to the archive's file, not as text
ALIAS_LINE = re.compile(r'^alias (?:_root_\.)?(\S+) := (\S+)\n\Z', re.M)


def git(*args, check=True, binary=False, stdin=None):
    p = subprocess.run(['git', '-C', C.PROOF, '-c', 'core.quotePath=false'] + list(args), stdout=subprocess.PIPE,
                       check=check, input=stdin)
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
    """Character spans of `old` to replace, and what replaces them: [(start, old length, new text)].

    Changed regions are found line by line; inside each region the characters that old and new
    share at the start and at the end are left out, so only the part that really changed is kept.
    Offsets are in `old + "\\n"` (every line then ends with a newline)."""
    a, b = old.split('\n'), new.split('\n')
    A, B = old + '\n', new + '\n'
    pos_a, pos_b = [0], [0]
    for l in a:
        pos_a.append(pos_a[-1] + len(l) + 1)
    for l in b:
        pos_b.append(pos_b[-1] + len(l) + 1)
    out = []
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
        if tag == 'equal':
            continue
        x, y = A[pos_a[i1]:pos_a[i2]], B[pos_b[j1]:pos_b[j2]]
        pre = 0
        while pre < len(x) and pre < len(y) and x[pre] == y[pre]:
            pre += 1
        suf = 0
        while suf < len(x) - pre and suf < len(y) - pre and x[-1 - suf] == y[-1 - suf]:
            suf += 1
        out.append((pos_a[i1] + pre, len(x) - pre - suf, y[pre:len(y) - suf]))
    return out


def pieces(A, text):
    """Replacing text as pieces: text we wrote, and (position, length) for every run of MIN_COPY or more
    characters that also occurs in the archive's file A. None when there is no such run."""
    k, n = MIN_COPY, len(text)
    if n < k or len(A) < k:
        return None
    out, lit, i, found = [], [], 0, False
    while i < n:
        p = A.find(text[i:i + k]) if i + k <= n else -1
        if p < 0:
            lit.append(text[i])
            i += 1
            continue
        best_p, best_len, tries = p, 0, 0
        while p >= 0 and tries < 16:                 # the longest run among the first few places it occurs
            m = k
            while i + m < n and p + m < len(A) and text[i + m] == A[p + m]:
                m += 1
            if m > best_len:
                best_p, best_len = p, m
            tries += 1
            p = A.find(text[i:i + k], p + 1)
        if lit:
            out.append(''.join(lit))
            lit = []
        out.append((best_p, best_len))
        found = True
        i += best_len
    if lit:
        out.append(''.join(lit))
    return out if found else None


def block(path, old, new):
    """One file's entry in changes.patch. old is None for a file we added."""
    parts = [f'== {path} {sha(old) if old is not None else "new"} {sha(new)}\n']
    A = old + '\n' if old is not None else ''
    for start, length, text in hunks(old if old is not None else '', new):
        ps = pieces(A, text)
        if ps is None:
            parts.append(f'@@ {start} {length} {len(text)}\n{text}\n')
        else:
            parts.append(f'@% {start} {length} {len(ps)}\n')
            for q in ps:
                parts.append(f'+ {len(q)}\n{q}\n' if isinstance(q, str) else f'= {q[0]} {q[1]}\n')
    return ''.join(parts)


def parse_blocks(text):
    """-> [(path, old sha or 'new', new sha, [(start, old length, new text or list of pieces)])]
    A piece is text, or (position, length) in the archive's file."""
    blocks, i, n = [], 0, len(text)
    while i < n:
        j = text.index('\n', i)
        line = text[i:j]
        i = j + 1
        if line.startswith('== '):
            path, old_sha, new_sha = line[3:].rsplit(' ', 2)
            blocks.append((path, old_sha, new_sha, []))
        elif line.startswith('@@ '):
            start, length, size = (int(x) for x in line[3:].split(' '))
            blocks[-1][3].append((start, length, text[i:i + size]))
            i += size + 1
        elif line.startswith('@% '):
            start, length, count = (int(x) for x in line[3:].split(' '))
            ps = []
            for _ in range(count):
                j = text.index('\n', i)
                head = text[i:j]
                i = j + 1
                if head.startswith('+ '):
                    size = int(head[2:])
                    ps.append(text[i:i + size])
                    i += size + 1
                elif head.startswith('= '):
                    a, b = head[2:].split(' ')
                    ps.append((int(a), int(b)))
                else:
                    raise ValueError(f'unexpected piece in changes.patch: {head[:60]!r}')
            blocks[-1][3].append((start, length, ps))
        elif line:
            raise ValueError(f'unexpected line in changes.patch: {line[:60]!r}')
    return blocks


def patched(old, hs):
    A = old + '\n'
    t = A
    for start, length, text in sorted(hs, key=lambda h: h[0], reverse=True):   # from the end: earlier offsets stay valid
        if not isinstance(text, str):
            text = ''.join(q if isinstance(q, str) else A[q[0]:q[0] + q[1]] for q in text)
        t = t[:start] + text + t[start + length:]
    return t[:-1]


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
    n_chg = len(parse_blocks(changes))
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
