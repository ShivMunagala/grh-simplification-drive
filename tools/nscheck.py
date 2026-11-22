#!/usr/bin/env python3
"""Namespaces: can a change that registers a namespace alter what any other file means?

  tools/nscheck.py build                       # once: which base module registers which namespace
  tools/nscheck.py check --modules list.txt --new build/batch/new
  tools/nscheck.py opens GlobalTheory.T        # commands in the tree that could resolve to it

Why this exists. Lean keeps a list of registered namespaces. The only thing that reads it is the
resolution of `open X` / `export X` (plus editor completion and one linter): `open X` opens every
registered namespace `P.X` where `P` is an enclosing namespace or an already opened one. So a
module that newly registers a namespace can change what an `open` elsewhere refers to, without
changing any statement. The equivalence check therefore reports namespaces a recompiled module
registers that its old version did not.

Such an addition is harmless in two cases, which this tool decides:

  1. The namespace is already registered by a module that the changed module imports (directly
     or not). Then every file that sees the changed module already saw the namespace.
  2. No `open` or `export` command anywhere in the tree names a proper suffix of it (for
     `A.B.C`: `C` or `B.C`). Then nothing can newly resolve to it. (A command naming all of
     `A.B.C` already needed it to exist; if it resolved somewhere else before, case 1 or this
     listing shows it.)

A removed namespace is never harmless, except the root entry that `theorem _root_.X ...`
registers, which nothing can open.
"""
import argparse, collections, os, re, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C

TABLE = os.path.join(C.DATA_BASE, 'namespaces.tsv.zst')
ROOT_ENTRY = '[anonymous]'
OPEN = re.compile(r"(?<![\w.'])(open|export)\s+((?:scoped\s+)?(?:[A-Za-z_][\w.'!?₀-₉]*[ \t]*)+)")
STOP = {'in', 'hiding', 'renaming'}


def zlines(path):
    p = subprocess.Popen(['zstd', '-dc', path], stdout=subprocess.PIPE)
    for line in p.stdout:
        yield line
    p.wait()


def build(jobs=3):
    """Read every compiled base module (names only, fast) and write module, imports, namespaces."""
    mods = []
    for dp, dn, fn in os.walk(C.COMPILED):
        for f in fn:
            if f.endswith('.olean'):
                p = os.path.join(dp, f)
                mods.append((os.path.relpath(p, C.COMPILED)[:-6].replace(os.sep, '.'), p))
    mods.sort()
    chunks = [mods[i::jobs] for i in range(jobs)]
    procs = []
    for ch in chunks:
        cmd = C.sandbox([C.MODDUMP, '--nsonly'], ro=[os.path.dirname(C.MODDUMP), C.ROOT])
        p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        procs.append((p, ''.join(f'{m}\t{path}\n' for m, path in ch).encode()))
    import threading
    outs = [None] * len(procs)

    def run(i):
        outs[i] = procs[i][0].communicate(procs[i][1])[0]

    ts = [threading.Thread(target=run, args=(i,)) for i in range(len(procs))]
    for t in ts:
        t.start()
    for t in ts:
        t.join()
    z = subprocess.Popen(['zstd', '-q', '-3', '-f', '-o', TABLE], stdin=subprocess.PIPE)
    n = errors = 0
    for out in outs:
        for line in out.split(b'\n'):
            if line[:1] in (b'M', b'N', b'A'):
                z.stdin.write(line + b'\n')
                n += line[:1] == b'M'
            elif line[:1] == b'X':
                errors += 1
    z.stdin.close(); z.wait()
    print(f'{n} modules read, {errors} could not be read; table: {TABLE}')


def load():
    """-> (imports: {module: [modules]}, registers: {module: set(namespaces)})."""
    if not os.path.exists(TABLE):
        sys.exit('no namespace table yet: run tools/nscheck.py build')
    imports, registers = {}, {}
    for line in zlines(TABLE):
        f = line.rstrip(b'\n').split(b'\t')
        if f[0] == b'M':
            imports[f[1].decode()] = f[3].decode().split(',') if len(f) > 3 and f[3] else []
        elif f[0] == b'N':
            registers[f[1].decode()] = set(f[2].decode().split(',')) if len(f) > 2 and f[2] else set()
    return imports, registers


def load_entries():
    """-> {module: {extension: number of entries}}: what each module of the unmodified archive registers
    with Lean (instances, simp lemmas, notation, tagged lemmas and so on), from the same table."""
    if not os.path.exists(TABLE):
        sys.exit('no namespace table yet: run tools/nscheck.py build')
    entries = {}
    for line in zlines(TABLE):
        f = line.rstrip(b'\n').split(b'\t')
        if f[0] == b'A':
            d = {}
            for kv in (f[2].decode().split(',') if len(f) > 2 and f[2] else []):
                k, _, v = kv.rpartition('=')
                d[k] = int(v) if v.isdigit() else 1
            entries[f[1].decode()] = d
    return entries


def seen_by(imports, registers, namespace, extra_registers=None):
    """Set of modules whose imports (direct or not) register `namespace`; a module that registers
    it itself does not count for itself. extra_registers: {module: set} overriding the table."""
    reg = dict(registers)
    reg.update(extra_registers or {})
    has = {}                                  # module -> registered by itself or below

    def below(m):
        stack = [(m, iter(imports.get(m, ())))]
        while stack:
            cur, it = stack[-1]
            advanced = False
            for i in it:
                if i not in has:
                    if i not in imports:
                        has[i] = False        # Mathlib, Lean: not in the tree
                        continue
                    stack.append((i, iter(imports.get(i, ()))))
                    advanced = True
                    break
            if not advanced:
                stack.pop()
                has[cur] = (namespace in reg.get(cur, ())) or any(has.get(i, False) for i in imports.get(cur, ()))
        return has[m]

    for m in imports:
        if m not in has:
            below(m)
    return {m for m in imports if any(has.get(i, False) for i in imports.get(m, ()))}


def open_commands(names, src=C.SRC):
    """Every `open` / `export` in the tree naming a suffix of one of the given namespaces.
    -> {(command, id written, 'proper suffix' | 'whole name'): [files]}"""
    suffixes = {}
    for n in names:
        parts = n.split('.')
        for k in range(1, len(parts) + 1):
            suffixes.setdefault('.'.join(parts[-k:]), set()).add('whole name' if k == len(parts) else 'proper suffix')
    last = {s.split('.')[-1] for s in suffixes}
    hits = collections.defaultdict(list)
    for dp, dn, fn in os.walk(src):
        for f in fn:
            if not f.endswith('.lean'):
                continue
            p = os.path.join(dp, f)
            with open(p, encoding='utf-8', errors='replace') as fh:
                text = fh.read()
            if 'open' not in text and 'export' not in text:
                continue
            if not any(w in text for w in last):
                continue
            for m in OPEN.finditer(text):
                for tok in m.group(2).split():
                    if tok == 'scoped':
                        continue
                    if tok in STOP:
                        break
                    tok = tok[7:] if tok.startswith('_root_.') else tok
                    for kind in suffixes.get(tok, ()):
                        hits[(m.group(1), tok, kind)].append(os.path.relpath(p, src))
    return hits


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    b = sub.add_parser('build'); b.add_argument('--jobs', type=int, default=3)
    o = sub.add_parser('opens'); o.add_argument('namespaces', nargs='+')
    c = sub.add_parser('check')
    c.add_argument('--modules', required=True, help='file with one changed module per line')
    c.add_argument('--new', required=True, help='root of the recompiled modules')
    a = ap.parse_args()
    if a.cmd == 'build':
        build(a.jobs)
    elif a.cmd == 'opens':
        for k, v in sorted(open_commands(a.namespaces).items(), key=lambda kv: -len(kv[1])):
            print(k, len(v), v[:3])
    else:
        with open(a.modules) as fh:
            mods = [l.strip() for l in fh if l.strip()]
        imports, registers = load()
        added = collections.defaultdict(list)       # namespace -> modules that newly register it
        for i in range(0, len(mods), 4000):
            chunk = mods[i:i + 4000]
            pairs = [(m, C.module_path(m, a.new, '.olean')) for m in chunk]
            parsed = C.parse_consts(C.moddump(pairs, extra=('--nsonly',)))
            for m in chunk:
                new = set(parsed.get(m, {}).get('namespaces') or ())
                for n in new - registers.get(m, set()) - {ROOT_ENTRY}:
                    added[n].append(m)
        really_new = []
        for n, ms in sorted(added.items()):
            seen = seen_by(imports, registers, n)
            fresh = [m for m in ms if m not in seen]
            print(f'{n}: newly registered by {len(ms)} modules; {len(ms) - len(fresh)} of them already import a '
                  f'module that registers it; {len(fresh)} do not')
            if fresh:
                really_new.append(n)
                print('   e.g.', fresh[:3])
        if really_new:
            hits = open_commands(really_new)
            risky = {k: v for k, v in hits.items() if k[2] == 'proper suffix'}
            print(f'commands naming a proper suffix of {really_new}: {sum(len(v) for v in risky.values())}')
            for k, v in sorted(risky.items(), key=lambda kv: -len(kv[1]))[:20]:
                print('  ', k, len(v), v[:3])
            whole = {k: v for k, v in hits.items() if k[2] == 'whole name'}
            for k, v in sorted(whole.items(), key=lambda kv: -len(kv[1]))[:10]:
                print('   whole name:', k, len(v), v[:2])
            sys.exit(2 if risky else 0)


if __name__ == '__main__':
    main()
