#!/usr/bin/env python3
"""Turn restating wrappers into aliases.

The archive has tens of thousands of files of this shape:

    set_option maxHeartbeats 1000000 in
    theorem _root_.GlobalTheory.T.some_name : <the full statement again> := by
      first | exact @Original.name | exact Original.name | (intros; apply Original.name <;> assumption)

When the restated statement is identical to the statement of `Original.name`, the wrapper says
nothing new. This tool rewrites such a file to

    alias _root_.GlobalTheory.T.some_name := Original.name

which declares the same theorem with the same statement, so no other file can tell the difference,
and drops the duplicated statement from the source.

  tools/alias_wrappers.py find  --out list.tsv     list wrappers whose statement equals the original's
                                                   (from the tables; nothing is compiled)
  tools/alias_wrappers.py apply --list list.tsv [--limit N]   rewrite those files in proof/src

Rewriting does not prove anything by itself: every rewritten file still has to be compiled and
checked like any other change.
"""
import argparse, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C
import cone as CONE


def pattern(wrapper, target):
    w, t = re.escape(wrapper), re.escape(target)
    return re.compile(
        r'(?:^set_option maxHeartbeats \d+ in[ \t]*\n)?'
        r'^theorem (?P<root>_root_\.)?' + w + r' :.*?\n'
        r'[ \t]+first \| exact @(?:_root_\.)?' + t + r' \| exact (?:_root_\.)?' + t +
        r' \| \(intros; apply (?:_root_\.)?' + t + r' <;> assumption\)\s*\Z',
        re.M | re.S)


def rewrite(text, wrapper, target):
    """Return the rewritten file text, or None if the file does not have the expected shape."""
    m = pattern(wrapper, target).search(text)
    if not m:
        return None
    head = text[:m.start()]
    if re.search(r'^\s*(namespace|section)\b', head, re.M):
        return None                               # keep it simple: only files with the theorem at top level
    return head + f'alias {m.group("root") or ""}{wrapper} := {target}\n'


def find(out):
    worklist = os.path.join(C.ROOT, 'build', 'judge', 'worklist.tsv.zst')
    rec = {}
    for line in CONE.zlines(os.path.join(C.DATA_BASE, 'consts.tsv.zst')):
        if line[:1] == b'C':
            f = line.rstrip(b'\n').split(b'\t', 9)
            if len(f) == 10:
                rec.setdefault(f[9].decode('utf-8', 'replace'), (int(f[5]), int(f[3])))
    exact = re.compile(r'exact @(?:_root_\.)?([^\s|)]+)')
    rows = []
    for i, line in enumerate(CONE.zlines(worklist)):
        if i == 0:
            continue
        f = line.decode('utf-8', 'replace').rstrip('\n').split('\t')
        module, name, tokens = f[3], f[6], int(f[1])
        if not module.endswith('Statement') or name not in rec:
            continue
        try:
            with open(C.module_path(module), encoding='utf-8') as fh:
                text = fh.read()
        except OSError:
            continue
        m = exact.search(text)
        if not m or m.group(1) not in rec or rec[m.group(1)] != rec[name]:
            continue
        if rewrite(text, name, m.group(1)) is None:
            continue
        rows.append((tokens, module, name, m.group(1)))
    rows.sort(reverse=True)
    with open(out, 'w', encoding='utf-8') as fh:
        for r in rows:
            fh.write('\t'.join(str(x) for x in r) + '\n')
    print(f'{len(rows)} wrappers restate the original exactly and have the expected shape; '
          f'{sum(r[0] for r in rows)} source tokens in them')


def apply(list_path, limit):
    n = 0
    with open(list_path, encoding='utf-8') as fh:
        for line in fh:
            tokens, module, name, target = line.rstrip('\n').split('\t')
            p = C.module_path(module)
            with open(p, encoding='utf-8') as sf:
                text = sf.read()
            new = rewrite(text, name, target)
            if new is None:
                continue
            with open(p, 'w', encoding='utf-8') as sf:
                sf.write(new)
            n += 1
            if limit and n >= limit:
                break
    print(f'rewrote {n} files')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('command', choices=['find', 'apply'])
    ap.add_argument('--out', default=os.path.join(C.ROOT, 'build', 'wrappers.tsv'))
    ap.add_argument('--list', default=os.path.join(C.ROOT, 'build', 'wrappers.tsv'))
    ap.add_argument('--limit', type=int, default=0)
    a = ap.parse_args()
    if a.command == 'find':
        find(a.out)
    else:
        apply(a.list, a.limit)


if __name__ == '__main__':
    main()
