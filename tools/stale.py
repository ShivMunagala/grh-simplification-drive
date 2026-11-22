#!/usr/bin/env python3
"""stale.py: which statements have changed since the other machine was last brought up to date.

Files compiled on the rented machine are compiled against the accepted state THERE. If that state is
older than the one here, a file compiled there may have been checked against a statement that has
since been changed or removed here. data/overlay/stale.json lists those declarations; the judge refuses
a file compiled elsewhere that mentions one of them (unless it was compiled with the changed module in
place). tools/record.py adds to the list with every recorded change; tools/remote/sync_there.py empties
it when the other machine is brought up to date.

This tool rebuilds the list from the tables, for the case where it was not kept from the start:

  python3 tools/stale.py extract --modules FILE --out theirs.json     (on the other machine)
  python3 tools/stale.py build --theirs theirs.json --since COMMIT    (here)
"""
import argparse, json, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C
import cone as CONE

STALE = os.path.join(C.DATA_OVERLAY, 'stale.json')


def load():
    return (C.load_json(STALE, {}) or {}).get('ids', {})


def add(changed, commit=None):
    """Add {id: [name, module]} to the list (called when a change is recorded)."""
    data = C.load_json(STALE, {}) or {}
    ids = data.setdefault('ids', {})
    for i, (name, module) in changed.items():
        ids[str(i)] = {'name': name, 'module': module, 'change': commit}
    os.makedirs(C.DATA_OVERLAY, exist_ok=True)
    with open(STALE, 'w', encoding='utf-8') as fh:
        json.dump(data, fh, ensure_ascii=False, indent=0)
    return len(ids)


def reset(commit):
    os.makedirs(C.DATA_OVERLAY, exist_ok=True)
    with open(STALE, 'w', encoding='utf-8') as fh:
        json.dump({'since': commit, 'ids': {}}, fh)


def records(modules):
    """{module: {name: [kind, id, what users can see of it, the same with binder names and kinds or None]}} in
    the accepted state on this machine. The second form exists only for modules compiled by the judge."""
    want, rows, seen = set(modules), {}, set()
    overlay = os.path.join(C.DATA_OVERLAY, 'consts.tsv')
    for path, is_base in ((overlay, False), (os.path.join(C.DATA_BASE, 'consts.tsv.zst'), True)):
        if not os.path.exists(path):
            continue
        cur, keep, last = None, False, None
        for line in CONE.zlines(path):
            tag = line[:1]
            if tag == b'M':
                cur = line.split(b'\t')[1].decode()
                keep = cur in want and not (is_base and cur in seen)
                if keep and not is_base:
                    seen.add(cur)
                if keep:
                    rows.setdefault(cur, {})
            elif tag == b'C' and keep:
                f = line.rstrip(b'\n').split(b'\t', 9)
                if len(f) == 10:
                    kind = f[1].decode()
                    # a theorem is its statement; anything else can be unfolded, so its body counts too
                    sig = [int(f[3]), int(f[5])] + ([] if kind == 'thm' else [int(f[4]), int(f[6])])
                    last = rows[cur][f[9].decode('utf-8', 'replace')] = [kind, int(f[2]), sig, None]
            elif tag == b'S' and keep and last is not None:
                f = line.rstrip(b'\n').split(b'\t')
                if len(f) >= 5 and int(f[1]) == last[1]:
                    last[3] = [int(f[2]), int(f[4])] + ([] if last[0] == 'thm' else [int(f[3])])
    return rows


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)
    e = sub.add_parser('extract')
    e.add_argument('--modules', required=True)
    e.add_argument('--out', required=True)
    b = sub.add_parser('build')
    b.add_argument('--theirs', required=True)
    b.add_argument('--since', required=True, help='what the other machine holds (a label or commit)')
    a = ap.parse_args()
    if a.cmd == 'extract':
        with open(a.modules) as fh:
            mods = [l.strip() for l in fh if l.strip()]
        rows = records(mods)
        with open(a.out, 'w', encoding='utf-8') as fh:
            json.dump(rows, fh, ensure_ascii=False)
        print(f'{len(rows)} of {len(mods)} modules, {sum(len(v) for v in rows.values())} declarations written to {a.out}')
    else:
        with open(a.theirs, encoding='utf-8') as fh:
            theirs = json.load(fh)
        mine = records(list(theirs))
        ids, kinds = {}, {'removed': 0, 'changed': 0}
        for m, decls in theirs.items():
            new = mine.get(m, {})
            for name, (kind, i, sig, strict) in decls.items():
                n = new.get(name)
                if n is None or n[0] != kind or n[2] != sig or (strict and n[3] and n[3] != strict):
                    what = 'removed' if n is None else 'changed'
                    kinds[what] += 1
                    ids[str(i)] = {'name': name, 'module': m, 'change': what}
        os.makedirs(C.DATA_OVERLAY, exist_ok=True)
        with open(STALE, 'w', encoding='utf-8') as fh:
            json.dump({'since': a.since, 'ids': ids}, fh, ensure_ascii=False, indent=0)
        print(f'{len(theirs)} modules compared: {kinds["changed"]} declarations changed, {kinds["removed"]} are gone; '
              f'written to {STALE}')


if __name__ == '__main__':
    main()
