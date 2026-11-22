#!/usr/bin/env python3
"""try_auto.py: theorems stated in Mathlib terms only, proved again by one call of standard automation.

Many theorems the five targets need have statements that mention nothing of the archive: lemmas at library
level, proved by hand at length. This tool lists them and asks Lean, for each, whether a closing tactic
(simp, norm_num, omega, linarith, positivity, ring, aesop, grind, exact?, ...) proves the statement, and how
large the proof it builds is (tools/compact/GrhTry.lean). The answers become edits that replace the proof by
that one tactic; they go through tools/proof_edits.py variants and tools/batch_variants.py like every other
bulk sweep, so a new proof is used only if its file compiles to the same interface and is smaller.

  python3 tools/try_auto.py find --out build/auto/targets.json [--min-nodes 1000]
  python3 tools/try_auto.py run --targets build/auto/targets.json --work build/auto [--jobs 8] [--sample 400]
  python3 tools/try_auto.py edits --targets build/auto/targets.json --work build/auto --out build/auto/edits.jsonl
"""
import argparse, collections, hashlib, json, os, random, re, sys, time
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C
import cone as CONE
import proof_edits as PE

CD = PE.CD
TOOL = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'compact')
HELP = re.compile(r"(\._proof_\d|\._simp_\d|\.eq_\d+$|\.eq_def$|\._abel_\d|\._ring_\d|\.match_\d|\._auxLemma|\.congr_simp$)")


def say(msg, t0=[time.time()]):
    print(f'{msg}  [{time.time() - t0[0]:.0f}s]', flush=True)


def find(out, min_nodes):
    overlay = os.path.join(C.DATA_OVERLAY, 'consts.tsv')
    g = CONE.load_graph(C.DATA_BASE, overlay if os.path.exists(overlay) else None, (), say)
    by = CONE.find_names(g, set(C.TARGETS))
    cone = CONE.reach(g, [by[t] for t in C.TARGETS])
    targets = [{'module': g.modnames[g.mods[i]], 'name': g.names[i], 'proof': g.vsize[i], 'statement': g.tsize[i]}
               for i in range(g.n)
               if cone[i] and g.kinds[i] == 'thm' and g.t_off[i + 1] == g.t_off[i] and g.vsize[i] >= min_nodes
               and not HELP.search(g.names[i])]
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    with open(out, 'w', encoding='utf-8') as fh:
        json.dump(targets, fh, ensure_ascii=False)
    say(f'{len(targets):,} theorems stated in Mathlib terms only, with a proof of {min_nodes:,} nodes or more '
        f'({sum(t["proof"] for t in targets):,} nodes), in {len({t["module"] for t in targets}):,} files; written to {out}')


def lean_str(s):
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"') + '"'


def run(targets_file, work, jobs, sample, group, seed):
    os.environ['GRH_SLOTS'] = str(jobs)
    from compile_one import compile_module
    work = os.path.abspath(work)
    with open(targets_file, encoding='utf-8') as fh:
        targets = json.load(fh)
    res_dir, src_dir, out_dir = (os.path.join(work, d) for d in ('res', 'src', 'out'))
    os.makedirs(res_dir, exist_ok=True)
    done = set()
    for f in os.listdir(res_dir):
        with open(os.path.join(res_dir, f), encoding='utf-8') as fh:
            for line in fh:
                try:
                    done.add(json.loads(line)['name'])
                except (ValueError, KeyError):
                    pass
    todo = [t for t in targets if t['name'] not in done]
    if sample:
        random.Random(seed).shuffle(todo)
        todo = todo[:sample]
    by_mod = collections.defaultdict(list)
    for t in todo:
        by_mod[t['module']].append(t['name'])
    mods = sorted(by_mod)
    groups = [mods[i:i + group] for i in range(0, len(mods), group)]
    say(f'{len(todo):,} theorems to try in {len(mods):,} files, {len(groups):,} test files ({len(done):,} answered before)')
    tool_out = os.path.join(work, 'tool')
    r = compile_module('GrhTry', tool_out, src=TOOL, quiet=True)
    if not r['ok']:
        sys.exit('the trying command does not compile:\n' + r.get('messages_tail', ''))
    stamp = int(time.time())

    def one(k_ms):
        k, ms = k_ms
        name = f'GrhTryRun.T{stamp}_{k}'
        res = os.path.join(res_dir, f'T{stamp}_{k}.jsonl')
        text = ''.join(f'import {m}\n' for m in ms) + 'import GrhTry\n\n' + \
            ''.join(f'#grh_try {lean_str(n)} {lean_str(res)}\n' for m in ms for n in by_mod[m])
        p = C.module_path(name, src_dir)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, 'w', encoding='utf-8') as fh:
            fh.write(text)
        r = compile_module(name, out_dir, src=src_dir, overlays=[tool_out], quiet=True, timeout=7200, mem_gb=24.0)
        for ext in ('.olean', '.ilean'):
            q = C.module_path(name, out_dir, ext)
            if os.path.exists(q):
                os.remove(q)
        got = 0
        if os.path.exists(res):
            with open(res, encoding='utf-8') as fh:
                got = sum(1 for _ in fh)
        return ms, got, r

    asked = answered = 0
    retry = []
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        for n, (ms, got, r) in enumerate(pool.map(one, enumerate(groups)), 1):
            want = sum(len(by_mod[m]) for m in ms)
            asked += want; answered += got
            if got == 0 and len(ms) > 1:
                retry += [[m] for m in ms]              # (two files of a group may declare the same name)
            if n % 20 == 0:
                say(f'{n}/{len(groups)} test files, {answered:,} of {asked:,} theorems answered')
        if retry:
            say(f'{len(retry)} files again, one per test file')
            for ms, got, r in pool.map(one, enumerate(retry, len(groups))):
                answered += got
    say(f'{answered:,} of {asked:,} theorems answered')
    summary(targets_file, work)


def answers(work):
    res_dir = os.path.join(os.path.abspath(work), 'res')
    got = {}
    for f in sorted(os.listdir(res_dir)):
        with open(os.path.join(res_dir, f), encoding='utf-8') as fh:
            for line in fh:
                try:
                    j = json.loads(line)
                except ValueError:
                    continue
                got[j['name']] = j
    return got


def summary(targets_file, work):
    got = answers(work)
    with open(targets_file, encoding='utf-8') as fh:
        targets = {t['name']: t for t in json.load(fh)}
    tried = [j for j in got.values() if j.get('found') and j['name'] in targets]
    wins = [j for j in tried if j.get('wins')]
    better = [j for j in wins if min(w['size'] for w in j['wins']) < targets[j['name']]['proof']]
    print(f'  tried: {len(tried):,}; closed by a tactic: {len(wins):,} ({100 * len(wins) / max(1, len(tried)):.1f}%); '
          f'with a smaller proof: {len(better):,}')
    saved = sum(targets[j['name']]['proof'] - min(w['size'] for w in j['wins']) for j in better)
    print(f'  proof nodes of the tried theorems: {sum(targets[j["name"]]["proof"] for j in tried):,}; '
          f'nodes saved where the new proof is smaller: {saved:,}')
    by = collections.Counter(min(j['wins'], key=lambda w: w['size'])['tac'] for j in better)
    print('  by tactic (smallest proof):', by.most_common())


def edits(targets_file, work, out):
    got = answers(work)
    with open(targets_file, encoding='utf-8') as fh:
        targets = json.load(fh)
    overlay = os.path.join(C.DATA_OVERLAY, 'consts.tsv')
    g = CONE.load_graph(C.DATA_BASE, overlay if os.path.exists(overlay) else None, (), say)
    ranges = CD.load_ranges(g.patched)
    want = collections.defaultdict(list)
    for t in targets:
        j = got.get(t['name'])
        if not j or not j.get('wins'):
            continue
        w = min(j['wins'], key=lambda w: w['size'])
        if w['size'] < t['proof']:
            want[t['module']].append((t, w))
    mods = sorted(want)
    res, stats = [], collections.Counter()
    for lo in range(0, len(mods), 2000):
        texts = PE.texts_at(PE.accepted_commit(), mods[lo:lo + 2000])
        for m in mods[lo:lo + 2000]:
            src = texts.get(m)
            if src is None:
                continue
            lines = src.split('\n')
            for t, w in want[m]:
                r = ranges.get((m, t['name']))
                sp = PE.split_decl(src, lines, r) if r else None
                if sp is None:
                    stats['no source range, or the end of the statement was not found'] += 1
                    continue
                a, body_start, b = sp
                old = src[body_start:b]
                new = ' by ' + w['tac']
                if CONE.count_tokens(new) >= CONE.count_tokens(old):
                    stats['the proof is already that short'] += 1
                    continue
                stats['edits'] += 1
                res.append({'module': m, 'theorem': t['name'], 'first_line': src.count('\n', 0, body_start),
                            'first_col': 0, 'start': body_start, 'end': b,
                            'old_sha': hashlib.sha256(old.encode('utf-8')).hexdigest(), 'body': new,
                            'tag': 'auto', 'size': t['proof'], 'tokens': CONE.count_tokens(old)})
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    with open(out, 'w', encoding='utf-8') as fh:
        for e in res:
            fh.write(json.dumps(e, ensure_ascii=False) + '\n')
    for k, v in stats.items():
        print(f'  {k}: {v:,}')
    say(f'{len(res):,} edits in {len({e["module"] for e in res}):,} files written to {out}')


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)
    f = sub.add_parser('find')
    f.add_argument('--out', required=True)
    f.add_argument('--min-nodes', type=int, default=1000)
    r = sub.add_parser('run')
    r.add_argument('--targets', required=True); r.add_argument('--work', required=True)
    r.add_argument('--jobs', type=int, default=1)
    r.add_argument('--sample', type=int, default=0, help='try only this many, chosen at random')
    r.add_argument('--group', type=int, default=8, help='files of the archive per test file')
    r.add_argument('--seed', type=int, default=1)
    s = sub.add_parser('summary')
    s.add_argument('--targets', required=True); s.add_argument('--work', required=True)
    e = sub.add_parser('edits')
    e.add_argument('--targets', required=True); e.add_argument('--work', required=True); e.add_argument('--out', required=True)
    a = ap.parse_args()
    if a.cmd == 'find':
        find(a.out, a.min_nodes)
    elif a.cmd == 'run':
        run(a.targets, a.work, a.jobs, a.sample, a.group, a.seed)
    elif a.cmd == 'summary':
        summary(a.targets, a.work)
    else:
        edits(a.targets, a.work, a.out)


if __name__ == '__main__':
    main()
