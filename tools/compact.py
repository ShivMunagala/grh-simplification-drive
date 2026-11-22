#!/usr/bin/env python3
"""compact.py: declarations written out with every argument explicit, reprinted in ordinary form.

Some files of the archive hold machine-printed terms: every implicit argument and every instance is
spelled out (`@NumberField.RingOfIntegers F inst`), so a term of a few thousand nodes takes tens of
thousands of tokens. This tool reprints such a declaration with Lean's ordinary printer and keeps the
new text only if Lean, reading it at the same place in the same file, builds exactly the same
statement and (for a definition) the same value. The check is done by tools/compact/GrhCompact.lean.

  python3 tools/compact.py find  --out build/compact/targets.json
  python3 tools/compact.py print --targets build/compact/targets.json --work build/compact --jobs 8
        -> <work>/edits.jsonl: one edit per declaration that printed back. They go through
           tools/proof_edits.py variants and tools/batch_variants.py like every other bulk sweep, so
           a new text is only used if its file compiles to the same interface and is not larger.
"""
import argparse, collections, hashlib, json, os, re, sys, time
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C
import cone as CONE
import proof_edits as PE

CD = PE.CD
HEADER = re.compile(r"\A(?P<head>(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev)\s+)"
                    r"(?P<name>[^\s:({\[⦃]+?)(?P<univ>\.\{[^}]*\})?[ \t]*:[ \t]*\n")
PREFIX = re.compile(r"\A(?:@\[[^\]]*\]\s*|private\s+|protected\s+|noncomputable\s+)*\Z")
TOOL = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'compact')


def say(msg, t0=[time.time()]):
    print(f'{msg}  [{time.time() - t0[0]:.0f}s]', flush=True)


def find(out, min_tokens, per_at, min_ats):
    """Declarations of the form `<keywords> name :` + statement + `:=` + term whose text is dense in `@`."""
    cand = []
    for dp, _, fn in os.walk(C.SRC):
        for f in fn:
            if f.endswith('.lean'):
                p = os.path.join(dp, f)
                with open(p, 'rb') as fh:
                    if fh.read().count(b'@') >= min_ats:
                        cand.append(os.path.relpath(p, C.SRC)[:-5].replace(os.sep, '.'))
    say(f'{len(cand):,} files hold {min_ats} or more `@`')
    overlay_consts = os.path.join(C.DATA_OVERLAY, 'consts.tsv')
    g = CONE.load_graph(C.DATA_BASE, overlay_consts if os.path.exists(overlay_consts) else None, (), say)
    ranges = CD.load_ranges(g.patched)
    by_mod = collections.defaultdict(list)
    want = set(cand)
    for (m, name), r in ranges.items():
        if m in want:
            by_mod[m].append((name, r))
    targets, stats = [], collections.Counter()
    for lo in range(0, len(cand), 2000):
        texts = PE.texts_at(PE.accepted_commit(), cand[lo:lo + 2000])
        for m in cand[lo:lo + 2000]:
            src = texts.get(m)
            if src is None:
                continue
            lines = src.split('\n')
            starts = [0]
            for l in lines:
                starts.append(starts[-1] + len(l) + 1)
            for name, r in sorted(by_mod.get(m, ()), key=lambda x: x[1]):
                try:
                    a, b = CD.offset(lines, r[0], r[1]), CD.offset(lines, r[2], r[3])
                except IndexError:
                    stats['range outside the file'] += 1
                    continue
                if PREFIX.match(src[starts[r[0]]:a]):
                    a = starts[r[0]]                     # keywords and attributes before the range belong to it
                seg = src[a:b]
                h = HEADER.match(seg + '\n')
                if not h:
                    continue
                tokens = CONE.count_tokens(seg)
                if tokens < min_tokens or seg.count('@') * per_at < tokens:
                    continue
                k = CD.statement_end(seg)                # just after the `:=` that ends the statement
                if k is None or k < h.end():
                    stats['statement end not found'] += 1
                    continue
                # commands of the form `... in` right above the declaration act on it; they are repeated
                # in front of the check so that it reads the new text in the same scope
                pre, ln = [], src.count('\n', 0, a) - 1
                while ln >= 0 and lines[ln].rstrip().endswith(' in') and lines[ln][:1] not in (' ', '\t', ''):
                    pre.insert(0, lines[ln])
                    ln -= 1
                stats['declarations'] += 1
                stats['tokens'] += tokens
                targets.append({'module': m, 'name': name, 'written': h.group('name'), 'head': h.group('head'),
                                'univ': h.group('univ') or '', 'start': a, 'end': b, 'tokens': tokens, 'in': pre,
                                'statement': dedent4(seg[h.end():k - 2].rstrip()), 'value': dedent4(seg[k:].strip('\n')),
                                'old_sha': hashlib.sha256(seg.encode('utf-8')).hexdigest()})
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    with open(out, 'w', encoding='utf-8') as fh:
        json.dump(targets, fh, ensure_ascii=False)
    for k, v in stats.items():
        print(f'  {k}: {v:,}')
    say(f'{len(targets):,} declarations in {len({t["module"] for t in targets}):,} files written to {out}')


def dedent4(s):
    """The text as it stands in the file, moved to the left margin (the checking command indents it again by
    four). The first line starts right after `:` or `:=`; the others keep their indentation relative to each
    other, which matters for tactic blocks."""
    lines = s.split('\n')
    rest = [l for l in lines[1:] if l.strip()]
    cut = min((len(l) - len(l.lstrip(' ')) for l in rest), default=0)
    return '\n'.join([lines[0].lstrip(' ')] + [l[cut:] if l.strip() else '' for l in lines[1:]])


def lean_str(s):
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n') + '"'


def instrument(src, targets, out_file):
    """The file with `import GrhCompact` and a check after each target declaration."""
    for t in sorted(targets, key=lambda t: -t['end']):
        cmd = ''.join(l + '\n' for l in t['in']) + \
            (f"#grh_compact {lean_str(t['head'])} {t['written']} {lean_str(t['univ'])} {lean_str(out_file)} "
             f"{lean_str(t['statement'])} {lean_str(t['value'])}\n")
        src = src[:t['end']] + '\n' + cmd + src[t['end']:]
    imports = list(re.finditer(r'^import .*$', src, re.M))
    k = imports[-1].end() if imports else 0
    return src[:k] + ('\n' if imports else '') + 'import GrhCompact\n' + src[k:]


def answers(res_file):
    got = {}
    if os.path.exists(res_file):
        with open(res_file, encoding='utf-8') as fh:
            for line in fh:
                try:
                    j = json.loads(line)
                except ValueError:
                    continue                             # (a line cut off when a run was stopped)
                got[j.get('name')] = j
    return got


def print_back(targets_file, work, jobs, only, prior=None):
    os.environ['GRH_SLOTS'] = str(jobs)
    from compile_one import compile_module
    work = os.path.abspath(work)
    with open(targets_file, encoding='utf-8') as fh:
        targets = json.load(fh)
    by_mod = collections.defaultdict(list)
    for t in targets:
        if not only or t['module'] in only:
            by_mod[t['module']].append(t)
    tool_out = os.path.join(work, 'tool')
    r = compile_module('GrhCompact', tool_out, src=TOOL, quiet=True)
    if not r['ok']:
        sys.exit('the checking command does not compile:\n' + r.get('messages_tail', ''))
    say('checking command compiled')
    mods = sorted(by_mod)
    texts = {}
    for lo in range(0, len(mods), 2000):
        texts.update(PE.texts_at(PE.accepted_commit(), mods[lo:lo + 2000]))
    src_dir, out_dir, res_dir = (os.path.join(work, d) for d in ('src', 'out', 'res'))
    os.makedirs(res_dir, exist_ok=True)

    def one(m):
        res = os.path.join(res_dir, m + '.jsonl')
        if os.path.exists(res):
            os.remove(res)
        ts = [t for t in by_mod[m]
              if hashlib.sha256(texts[m][t['start']:t['end']].encode('utf-8')).hexdigest() == t['old_sha']]
        # declarations an earlier (stopped) run already answered are not asked again
        old = answers(os.path.join(prior, m + '.jsonl')) if prior else {}
        ask = [t for t in ts if t['name'] not in old and CD.user_name(t['name']) not in old]
        if not ask:
            return m, {'ok': True}, ts
        ts_all, ts = ts, ask
        p = C.module_path(m, src_dir)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, 'w', encoding='utf-8') as fh:
            fh.write(instrument(texts[m], ts, res))
        r = compile_module(m, out_dir, src=src_dir, overlays=[tool_out], quiet=True, timeout=7200, mem_gb=24.0)
        for ext in ('.olean', '.ilean'):                # the compiled file itself is of no use
            q = C.module_path(m, out_dir, ext)
            if os.path.exists(q):
                os.remove(q)
        return m, r, ts_all

    edits, stats, why = [], collections.Counter(), collections.Counter()
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        for n, (m, r, ts) in enumerate(pool.map(one, mods), 1):
            got = answers(os.path.join(prior, m + '.jsonl')) if prior else {}
            got.update(answers(os.path.join(res_dir, m + '.jsonl')))
            if not r['ok']:
                stats['files that did not compile with the checks in'] += 1
                print(f'  {m}: {r.get("messages_tail", "")[-300:]}', flush=True)
            for t in ts:
                j = got.get(t['name']) or got.get(CD.user_name(t['name']))
                stats['declarations tried'] += 1
                if not j:
                    why['no answer'] += 1
                    continue
                if not j.get('ok'):
                    why[(j.get('why') or '?')[:60]] += 1
                    continue
                new = j['text'].rstrip('\n')
                new_tokens = CONE.count_tokens(new)
                if new_tokens >= t['tokens']:
                    why['printed back, but not shorter'] += 1
                    continue
                stats['declarations printed back'] += 1
                stats['tokens before'] += t['tokens']
                stats['tokens after'] += new_tokens
                stats[f"form: {j.get('form')}"] += 1
                stats['applications left explicit'] += j.get('explicit') or 0
                edits.append({'module': m, 'theorem': t['name'], 'first_line': texts[m].count('\n', 0, t['start']),
                              'first_col': 0, 'start': t['start'], 'end': t['end'], 'old_sha': t['old_sha'],
                              'body': new, 'tag': 'compact', 'size': 0, 'tokens': t['tokens']})
            if n % 10 == 0:
                say(f'{n}/{len(mods)} files')
    with open(os.path.join(work, 'edits.jsonl'), 'w', encoding='utf-8') as fh:
        for e in edits:
            fh.write(json.dumps(e, ensure_ascii=False) + '\n')
    for k, v in sorted(stats.items()):
        print(f'  {k}: {v:,}')
    for k, v in why.most_common():
        print(f'  not used, {k}: {v:,}')
    say(f'{len(edits):,} edits in {len({e["module"] for e in edits}):,} files written to {os.path.join(work, "edits.jsonl")}')


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)
    f = sub.add_parser('find')
    f.add_argument('--out', required=True)
    f.add_argument('--min-tokens', type=int, default=150)
    f.add_argument('--per-at', type=int, default=25, help='at least one `@` per this many tokens')
    f.add_argument('--min-ats', type=int, default=20, help='only files with this many `@`')
    p = sub.add_parser('print')
    p.add_argument('--targets', required=True)
    p.add_argument('--work', required=True)
    p.add_argument('--jobs', type=int, default=1)
    p.add_argument('--only', default=None, help='modules, comma separated')
    p.add_argument('--prior', default=None, help='res directory of an earlier run: its answers are reused')
    a = ap.parse_args()
    if a.cmd == 'find':
        find(a.out, a.min_tokens, a.per_at, a.min_ats)
    else:
        print_back(a.targets, a.work, a.jobs, set(a.only.split(',')) if a.only else None, a.prior)


if __name__ == '__main__':
    main()
