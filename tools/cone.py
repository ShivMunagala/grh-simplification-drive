#!/usr/bin/env python3
"""Compute the cone of the target theorems and the two size dials.

  tools/cone.py --data data/base --src proof/src --out data/base
  tools/cone.py --data data/base --src proof/src --out build/x \
      --patch-consts build/x/consts.tsv --patch-decls build/x/decls.tsv --removed-modules build/x/removed.txt

Reads the tables written by dump_stream.py:
  consts.tsv.zst   one record per compiled declaration (kind, sizes, what it mentions)
  decls.tsv.zst    source range of every declaration written in a source file
A patch replaces the records of the modules it contains (modules recompiled for a change);
removed modules are dropped.

The cone is everything outside Mathlib that the target theorems depend on, directly or through
other declarations. A declaration is "outside Mathlib" when it is defined in this tree; anything a
declaration mentions that is not defined here is Mathlib or Lean itself and is free.

Dials computed here:
  written-out size   sum over the cone of (statement nodes + body nodes) of the compiled terms
  source size        tokens of the source text of the cone's declarations (comments excluded,
                     a name of any length is one token)
Time, the third dial, is measured by the judge on the files it recompiles.

Outputs (in --out): summary.json, cone.tsv.zst (one row per declaration), modules.tsv.zst
"""
import argparse, array, collections, json, os, re, subprocess, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C

RH_ONLY = ['riemannHypothesis', 'riemannZeta_eq_zero_re']


def zlines(path):
    if path.endswith('.zst'):
        p = subprocess.Popen(['zstd', '-dc', path], stdout=subprocess.PIPE)
        for line in p.stdout:
            yield line
        p.wait()
    else:
        with open(path, 'rb') as fh:
            for line in fh:
                yield line


# ---------------------------------------------------------------- tokenizer
def strip_comments(s):
    """Remove `--` line comments and (nested) `/- -/` block comments, keeping string literals."""
    if '--' not in s and '/-' not in s:
        return s
    out = []
    i, n, depth = 0, len(s), 0
    while i < n:
        c = s[i]
        if depth:
            if s.startswith('/-', i):
                depth += 1; i += 2
            elif s.startswith('-/', i):
                depth -= 1; i += 2
            else:
                i += 1
            continue
        if c == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == '\\' else 1
            out.append(s[i:j + 1]); i = j + 1
        elif s.startswith('--', i):
            j = s.find('\n', i)
            i = n if j < 0 else j
        elif s.startswith('/-', i):
            depth = 1; i += 2
        else:
            out.append(c); i += 1
    return ''.join(out)


TOKEN = re.compile(
    r'"(?:\\.|[^"\\])*"'                               # string literal
    r"|«[^»]*»(?:\.(?:«[^»]*»|[^\W\d][\w'!?]*))*"       # quoted name, possibly dotted
    r"|[^\W\d][\w'!?]*(?:\.(?:«[^»]*»|[^\W\d][\w'!?]*|\d+))*"   # name, possibly dotted
    r"|\d+(?:\.\d+)?"                                   # number
    r"|[()\[\]{}⟨⟩,;]"                                  # brackets and separators, one each
    r"|[^\s\w()\[\]{}⟨⟩,;\"«»]+"                        # run of other symbols
    r"|\S")


def count_tokens(text):
    return len(TOKEN.findall(strip_comments(text)))


def u16_index(line, col):
    """Convert a UTF-16 column to a Python string index."""
    if col <= 0:
        return 0
    if line.isascii() or all(ord(ch) <= 0xFFFF for ch in line):
        return min(col, len(line))
    units = 0
    for i, ch in enumerate(line):
        if units >= col:
            return i
        units += 2 if ord(ch) > 0xFFFF else 1
    return len(line)


def slice_range(lines, sl, sc, el, ec):
    if sl >= len(lines):
        return ''
    el = min(el, len(lines) - 1)
    if sl == el:
        ln = lines[sl]
        return ln[u16_index(ln, sc):u16_index(ln, ec)]
    parts = [lines[sl][u16_index(lines[sl], sc):]]
    parts.extend(lines[sl + 1:el])
    parts.append(lines[el][:u16_index(lines[el], ec)])
    return '\n'.join(parts)


def pct(sorted_vals, q):
    if not sorted_vals:
        return 0
    return sorted_vals[min(len(sorted_vals) - 1, int(q * len(sorted_vals)))]


def distribution(vals):
    vals = sorted(vals)
    return {'count': len(vals), 'p50': pct(vals, 0.5), 'p90': pct(vals, 0.9), 'p95': pct(vals, 0.95),
            'p99': pct(vals, 0.99), 'p999': pct(vals, 0.999), 'max': vals[-1] if vals else 0}


# ---------------------------------------------------------------- core
class Graph:
    """Declarations defined in the tree and the references between them."""
    pass


def load_graph(data, patch_consts=None, removed=(), say=lambda m: None):
    base = os.path.join(data, 'consts.tsv.zst')
    patched = set()
    if patch_consts:
        for line in zlines(patch_consts):
            if line[:1] == b'M':
                patched.add(line.split(b'\t')[1].decode())
    skip = patched | set(removed)

    def records():
        """Yield ('M', name, imports) and ('C', fields, None) from base then patch, honouring skips."""
        for path, is_base in ((base, True), (patch_consts, False)):
            if not path:
                continue
            keep = True
            for line in zlines(path):
                tag = line[:1]
                if tag == b'M':
                    f = line.rstrip(b'\n').split(b'\t')
                    m = f[1].decode()
                    keep = not (is_base and m in skip)
                    if keep:
                        yield 'M', m, (f[3].decode().split(',') if len(f) > 3 and f[3] else [])
                elif tag == b'C' and keep:
                    f = line.rstrip(b'\n').split(b'\t', 9)
                    if len(f) == 10:
                        yield 'C', f, None
                elif tag == b'X' and keep:
                    yield 'X', line.decode('utf-8', 'replace').strip(), None

    g = Graph()
    # pass 1: declarations defined in the tree
    idx = {}
    g.names, g.mods, g.kinds = [], [], []
    g.tsize, g.vsize = array.array('q'), array.array('q')
    g.thash = array.array('Q')
    g.modnames, g.mod_imports = [], []
    g.dup = 0
    g.errors = []
    g.forbidden_uses = []
    cur = -1
    for tag, f, extra in records():
        if tag == 'M':
            g.modnames.append(f); g.mod_imports.append(extra); cur = len(g.modnames) - 1
        elif tag == 'C':
            h = int(f[2])
            if h in idx:
                g.dup += 1
                continue
            idx[h] = len(g.names)
            g.names.append(f[9].decode('utf-8', 'replace'))
            g.mods.append(cur); g.kinds.append(f[1].decode())
            g.tsize.append(int(f[3])); g.vsize.append(int(f[4])); g.thash.append(int(f[5]))
        else:
            g.errors.append(f)
    n = g.n = len(g.names)
    say(f'pass1: {n} declarations in {len(g.modnames)} modules, repeated auxiliaries={g.dup}, '
        f'module errors={len(g.errors)}')

    # pass 2: edges inside the tree (CSR), separately for statements and bodies
    g.t_off = array.array('q', [0]); g.t_edges = array.array('I')
    g.v_off = array.array('q', [0]); g.v_edges = array.array('I')
    g.base_refs = 0
    done = bytearray(n)
    for tag, f, extra in records():
        if tag != 'C':
            continue
        i = idx[int(f[2])]
        if done[i]:
            continue
        done[i] = 1
        if i != len(g.t_off) - 1:
            raise RuntimeError('record order changed between passes')
        for col, edges, off in ((7, g.t_edges, g.t_off), (8, g.v_edges, g.v_off)):
            if f[col]:
                for d in f[col].split(b' '):
                    d = int(d)
                    j = idx.get(d)
                    if j is None:
                        g.base_refs += 1
                        if d in C.FORBIDDEN:
                            g.forbidden_uses.append((g.names[i], C.FORBIDDEN[d]))
                    else:
                        edges.append(j)
            off.append(len(edges))
    say(f'pass2: statement edges={len(g.t_edges)}, body edges={len(g.v_edges)}, '
        f'references to Mathlib/Lean={g.base_refs}')
    g.patched, g.skip = patched, skip
    return g


def reach(g, roots):
    mark = bytearray(g.n)
    stack = list(roots)
    for r in stack:
        mark[r] = 1
    te, to, ve, vo = g.t_edges, g.t_off, g.v_edges, g.v_off
    while stack:
        i = stack.pop()
        for j in te[to[i]:to[i + 1]]:
            if not mark[j]:
                mark[j] = 1; stack.append(j)
        for j in ve[vo[i]:vo[i + 1]]:
            if not mark[j]:
                mark[j] = 1; stack.append(j)
    return mark


def find_names(g, wanted):
    wanted = set(wanted)
    return {nm: i for i, nm in enumerate(g.names) if nm in wanted}


def compute(data, src, out=None, patch_consts=None, patch_decls=None, removed=(), targets=None, verbose=True):
    targets = targets or C.TARGETS
    rh_only = [t for t in RH_ONLY if t in targets] or targets[:1]
    t0 = time.time()

    def say(msg):
        if verbose:
            print(f'{msg}  [{time.time() - t0:.0f}s]', flush=True)

    g = load_graph(data, patch_consts, removed, say)
    n, names, mods, kinds, modnames = g.n, g.names, g.mods, g.kinds, g.modnames
    tsize, vsize, thash = g.tsize, g.vsize, g.thash
    skip, patched = g.skip, g.patched
    base_refs, forbidden_uses, errors, dup = g.base_refs, g.forbidden_uses, g.errors, g.dup

    by_name = find_names(g, set(targets) | set(rh_only))
    missing = [t for t in targets if t not in by_name]
    if missing:
        raise RuntimeError(f'target theorems not found: {missing}')

    cone = reach(g, [by_name[t] for t in targets])
    cone_rh = reach(g, [by_name[t] for t in rh_only])
    say(f'cone: {sum(cone)} declarations; RH-only cone: {sum(cone_rh)}')

    # declaration ranges (base, then patch overriding its modules)
    ranges = {}
    for path, is_base in ((os.path.join(data, 'decls.tsv.zst'), True), (patch_decls, False)):
        if not path or not os.path.exists(path):
            continue
        for line in zlines(path):
            f = line.rstrip(b'\n').split(b'\t', 5)
            if len(f) == 6:
                m = f[0].decode()
                if is_base and m in skip:
                    continue
                ranges[(m, f[5].decode('utf-8', 'replace'))] = (int(f[1]), int(f[2]), int(f[3]), int(f[4]))
    say(f'declaration ranges: {len(ranges)}')

    def range_of(i):
        """Source range for declaration i: its own, or that of the nearest enclosing named declaration."""
        nm = names[i]
        m = modnames[mods[i]]
        while True:
            r = ranges.get((m, nm))
            if r is not None:
                return (m,) + r
            k = nm.rfind('.')
            if k < 0:
                return None
            nm = nm[:k]

    def dials(mark, want_dist=False):
        kinds_c = collections.Counter()
        tt = vv = 0
        rset = set()
        no_range = 0
        modset = set()
        written = []
        for i in range(n):
            if not mark[i]:
                continue
            kinds_c[kinds[i]] += 1
            tt += tsize[i]; vv += vsize[i]
            modset.add(mods[i])
            if want_dist:
                written.append(tsize[i] + vsize[i])
            r = range_of(i)
            if r is None:
                no_range += 1
            else:
                rset.add(r)
        byfile = collections.defaultdict(list)
        for r in rset:
            byfile[r[0]].append(r)
        tokens = lines_total = missing_files = 0
        per_decl_tokens = []
        for m, rs in byfile.items():
            try:
                with open(C.module_path(m, src), encoding='utf-8') as fh:
                    lines = fh.read().split('\n')
            except OSError:
                missing_files += 1
                continue
            rs.sort(key=lambda r: (r[1], r[2], -r[3], -r[4]))
            last_end = (-1, -1)
            for (_, sl, sc, el, ec) in rs:
                if (el, ec) <= last_end:
                    continue                      # nested inside a range already counted
                if (sl, sc) < last_end:
                    sl, sc = last_end
                k = count_tokens(slice_range(lines, sl, sc, el, ec))
                tokens += k
                lines_total += el - sl + 1
                if want_dist:
                    per_decl_tokens.append(k)
                last_end = (el, ec)
        res = {
            'declarations': sum(kinds_c.values()),
            'by_kind': dict(kinds_c),
            'modules_touched': len(modset),
            'written_out_size': tt + vv,
            'written_out_statements': tt,
            'written_out_bodies': vv,
            'source_tokens': tokens,
            'source_lines': lines_total,
            'source_ranges': len(rset),
            'declarations_without_source_range': no_range,
            'source_files_missing': missing_files,
        }
        if want_dist:
            res['per_declaration_written_out'] = distribution(written)
            res['per_declaration_source_tokens'] = distribution(per_decl_tokens)
        return res

    d_all = dials(cone, want_dist=True)
    say('dials for the five theorems done')
    d_rh = dials(cone_rh)
    say('dials for RH only done')

    summary = {
        'targets': targets,
        'target_statement_hashes': {t: thash[by_name[t]] for t in targets},
        'tree': {'declarations': n, 'modules': len(modnames),
                 'written_out_size': sum(tsize) + sum(vsize),
                 'by_kind': dict(collections.Counter(kinds))},
        'cone': d_all,
        'cone_rh_only': d_rh,
        'references_to_base': base_refs,
        'forbidden_uses': forbidden_uses[:50],
        'axioms_declared': [names[i] for i in range(n) if kinds[i] == 'ax'][:50],
        'module_read_errors': errors[:50],
        'repeated_auxiliaries': dup,
        'patched_modules': sorted(patched),
        'removed_modules': sorted(removed),
    }
    if out:
        os.makedirs(out, exist_ok=True)
        json.dump(summary, open(os.path.join(out, 'summary.json'), 'w'), indent=1)
        z = subprocess.Popen(['zstd', '-q', '-3', '-f', '-o', os.path.join(out, 'cone.tsv.zst')], stdin=subprocess.PIPE)
        z.stdin.write(b'in_cone\tin_rh_cone\tkind\tstatement_size\tbody_size\tmodule\tname\n')
        per_mod = collections.defaultdict(lambda: [0, 0, 0, 0, 0])
        for i in range(n):
            m = modnames[mods[i]]
            z.stdin.write(f'{cone[i]}\t{cone_rh[i]}\t{kinds[i]}\t{tsize[i]}\t{vsize[i]}\t{m}\t{names[i]}\n'.encode())
            pm = per_mod[mods[i]]
            w = tsize[i] + vsize[i]
            pm[0] += 1; pm[3] += w
            if cone[i]:
                pm[1] += 1; pm[4] += w
            if cone_rh[i]:
                pm[2] += 1
        z.stdin.close(); z.wait()
        z = subprocess.Popen(['zstd', '-q', '-3', '-f', '-o', os.path.join(out, 'modules.tsv.zst')], stdin=subprocess.PIPE)
        z.stdin.write(b'module\tdeclarations\tin_cone\tin_rh_cone\twritten_out\twritten_out_in_cone\n')
        for mi, m in enumerate(modnames):
            pm = per_mod.get(mi, [0, 0, 0, 0, 0])
            z.stdin.write(f'{m}\t{pm[0]}\t{pm[1]}\t{pm[2]}\t{pm[3]}\t{pm[4]}\n'.encode())
        z.stdin.close(); z.wait()
        say('tables written')
    return summary


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--data', default=C.DATA_BASE)
    ap.add_argument('--src', default=C.SRC)
    ap.add_argument('--out', default=None)
    ap.add_argument('--patch-consts', default=None)
    ap.add_argument('--patch-decls', default=None)
    ap.add_argument('--removed-modules', default=None, help='file with one removed module name per line')
    ap.add_argument('--targets', default=None, help='comma-separated override of the target theorems (testing)')
    a = ap.parse_args()
    removed = []
    if a.removed_modules and os.path.exists(a.removed_modules):
        removed = [l.strip() for l in open(a.removed_modules) if l.strip()]
    s = compute(a.data, a.src, a.out or a.data, a.patch_consts, a.patch_decls, removed,
                a.targets.split(',') if a.targets else None)
    print(json.dumps(s, indent=1))


if __name__ == '__main__':
    main()
