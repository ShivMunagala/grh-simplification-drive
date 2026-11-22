#!/usr/bin/env python3
"""Judge the working tree of proof/ against the accepted state.

  tools/judge.py [--only Module.A,Module.B] [--work build/judge] [--propagate] [--no-time]

The accepted state is the unmodified archive plus every change recorded so far (tools/record.py).
Its compiled form is the compiled base with the overlay on top; its tables are the base tables
with the overlay rows patched in. A new change is judged against that, so changes stack.

What it does, all on this machine:

 1. Lists the source files in proof/ changed, added or deleted since the accepted commit
    (committed or not). --only restricts the judgement to the named modules.
 2. Compiles each changed or added file on its own against the accepted state (sandboxed), and,
    for timing, the accepted version of each changed file as well (cached per file).
 3. Runs the small equivalence check on each recompiled module. If a module still exposes the
    same statements and definitions, nothing that uses it needs rebuilding. If not, the modules
    that actually use what changed are listed (and recompiled too with --propagate).
 4. Recomputes the cone and the two size dials with the recompiled modules patched in.
 5. Checks validity: no compile errors, no `sorry`, no new axioms, the five statements unchanged.
 6. Applies the rule (no dial may go up) and the two fences, and prints a verdict:
      invalid     does not prove the five theorems, or uses something forbidden
      incomplete  other modules use what changed and have not been recompiled yet
      accept      valid and no dial went up (progress if one went down)
      review      valid, but a dial went up or a fence was hit: needs a person

This is a fast pre-filter. The final word is a full rebuild with Comparator on a large machine.
"""
import argparse, collections, hashlib, json, os, re, shutil, subprocess, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C
import cone as CONE
import iface as IFACE
from compile_one import compile_module

NEW_SYNTAX = re.compile(r'^\+(?!\+\+).*\b(macro|macro_rules|syntax|notation|infix|infixl|infixr|prefix|postfix|'
                        r'elab|elab_rules|declare_syntax_cat|binder_predicate)\b')
IMPORT = re.compile(r"^\s*(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+)?([^\s]+)", re.M)
TIME_TOLERANCE = 0.05          # relative
TIME_SLACK_S = 2.0             # absolute, on top
# The one agreed trade between dials: source size may rise if the written-out size falls by at
# least this many nodes for every token added. (The cone averages about 15 nodes per token.)
EXCHANGE_NODES_PER_TOKEN = 1000
TIME_CACHE = os.path.join(C.ROOT, 'data', 'time_cache.json')


def git(*args):
    """git in the proof repository (proof/), whose tag `upstream` is the unmodified archive."""
    return subprocess.run(['git', '-C', C.PROOF] + list(args), stdout=subprocess.PIPE, check=True).stdout.decode()


def to_module(path):
    """`src/A/B.lean` (relative to proof/) -> `A.B`."""
    rel = os.path.relpath(os.path.join(C.PROOF, path), C.SRC)
    return rel[:-5].replace(os.sep, '.')


def to_path(module):
    return 'src/' + module.replace('.', '/') + '.lean'


def changed_files(base):
    mod, add, rem = [], [], []
    for line in git('diff', '--name-status', '--no-renames', base, '--', 'src').splitlines():
        st, path = line.split('\t', 1)
        if not path.endswith('.lean'):
            continue
        (mod if st == 'M' else add if st == 'A' else rem if st == 'D' else mod).append(to_module(path))
    for path in git('ls-files', '--others', '--exclude-standard', '--', 'src').splitlines():
        if path.endswith('.lean'):
            add.append(to_module(path))
    return sorted(set(mod)), sorted(set(add)), sorted(set(rem))


def imports_of(module, src=C.SRC):
    try:
        with open(C.module_path(module, src), encoding='utf-8') as fh:
            return IMPORT.findall(fh.read())
    except OSError:
        return []


def order_by_imports(modules):
    """Order modules so that a module comes after the changed modules it imports."""
    mset = set(modules)
    deps = {m: [i for i in imports_of(m) if i in mset] for m in modules}
    out, seen = [], set()

    def visit(m, stack=()):
        if m in seen or m in stack:
            return
        for d in deps[m]:
            visit(d, stack + (m,))
        seen.add(m); out.append(m)

    for m in modules:
        visit(m)
    return out


def table_blocks(path):
    """Yield (module, [lines]) for each module block of a consts table (plain or .zst)."""
    cur, buf = None, []
    for line in CONE.zlines(path):
        if line[:1] == b'M':
            if cur is not None:
                yield cur, buf
            cur, buf = line.split(b'\t')[1].decode(), [line]
        elif cur is not None:
            buf.append(line)
    if cur is not None:
        yield cur, buf


def users_of(ids, exclude_modules, overlay_mods, overlay_removed):
    """Which declarations of the accepted state (by module) mention any of the given ids?"""
    want = {str(i).encode() for i in ids}
    users = collections.defaultdict(list)
    sources = [(os.path.join(C.DATA_BASE, 'consts.tsv.zst'), exclude_modules | overlay_mods | overlay_removed)]
    overlay_consts = os.path.join(C.DATA_OVERLAY, 'consts.tsv')
    if os.path.exists(overlay_consts):
        sources.append((overlay_consts, exclude_modules))
    for path, skip in sources:
        cur, keep = None, True
        for line in CONE.zlines(path):
            tag = line[:1]
            if tag == b'M':
                cur = line.split(b'\t')[1].decode()
                keep = cur not in skip
            elif tag == b'C' and keep:
                f = line.rstrip(b'\n').split(b'\t', 9)
                if len(f) != 10:
                    continue
                if (f[7] and not want.isdisjoint(f[7].split(b' '))) or (f[8] and not want.isdisjoint(f[8].split(b' '))):
                    users[cur].append(f[9].decode('utf-8', 'replace'))
    return users


def decl_tokens(module, name, ranges, src=C.SRC, cache={}):
    r = ranges.get((module, name))
    if r is None:
        return None
    if module not in cache:
        try:
            with open(C.module_path(module, src), encoding='utf-8') as fh:
                cache[module] = fh.read().split('\n')
        except OSError:
            cache[module] = []
    return CONE.count_tokens(CONE.slice_range(cache[module], *r))


def sha(text):
    return hashlib.sha256(text if isinstance(text, bytes) else text.encode('utf-8')).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--base', default=None,
                    help='commit in proof/ to compare with (default: the accepted commit, or the unmodified archive)')
    ap.add_argument('--only', default=None, help='comma-separated modules: judge only these changed files')
    ap.add_argument('--work', default=os.path.join(C.ROOT, 'build', 'judge'))
    ap.add_argument('--baseline', default=os.path.join(C.ROOT, 'baseline'))
    ap.add_argument('--propagate', action='store_true', help='also recompile modules that use what changed')
    ap.add_argument('--no-time', action='store_true', help='skip timing of the accepted versions')
    ap.add_argument('--threads', type=int, default=1)
    ap.add_argument('--mem-gb', type=float, default=8.0)
    ap.add_argument('--max-propagate', type=int, default=50)
    a = ap.parse_args()

    t0 = time.time()
    base_summary = C.load_json(os.path.join(a.baseline, 'summary.json'))
    state = C.accepted_state()
    base = a.base or (state['proof_commit'] if state else C.UPSTREAM_TAG)
    base_commit = git('rev-parse', base + '^{commit}').strip()
    upstream_commit = git('rev-parse', C.UPSTREAM_TAG + '^{commit}').strip()
    if state:
        if base_commit != state['proof_commit']:
            sys.exit(f"the accepted state on disk is for proof commit {state['proof_commit'][:8]}, "
                     f"but the base is {base_commit[:8]}; judge against the accepted commit")
        overlay_mods, overlay_removed = set(state['modules']), set(state['removed'])
        before = state['dials']
    else:
        if base_commit != upstream_commit:
            sys.exit('nothing has been recorded yet, so the base must be the unmodified archive (tag upstream)')
        overlay_mods, overlay_removed = set(), set()
        before = {k: base_summary['cone'][k] for k in ('source_tokens', 'written_out_size')} if base_summary else None

    work = os.path.abspath(a.work)
    shutil.rmtree(work, ignore_errors=True)
    new_dir, old_dir, oldsrc = (os.path.join(work, d) for d in ('new', 'old', 'oldsrc'))
    for d in (new_dir, old_dir, oldsrc):
        os.makedirs(d)
    report = {'base': base_commit, 'problems': [], 'notes': []}

    modified, added, removed = changed_files(base)
    src_override = {}          # files edited in the working tree but not part of this judgement
    if a.only:
        only = set(a.only.split(','))
        skipped = [m for m in modified + added + removed if m not in only]
        if skipped:
            report['notes'].append(f'{len(skipped)} other changed files ignored because of --only')
        for m in skipped:
            try:
                src_override[m] = git('show', f'{base}:{to_path(m)}')     # judged as they are in the base
            except subprocess.CalledProcessError:
                pass                                                         # new file: not in any table
        modified, added, removed = ([m for m in l if m in only] for l in (modified, added, removed))
    report['modified'], report['added'], report['removed'] = modified, added, removed
    print(f'changed: {len(modified)} modified, {len(added)} added, {len(removed)} deleted')
    if not (modified or added or removed):
        print('nothing changed')
        return
    report['changed_hashes'] = {}
    for m in modified + added:
        with open(C.module_path(m), 'rb') as fh:
            report['changed_hashes'][to_path(m)] = sha(fh.read())
    for m in removed:
        report['changed_hashes'][to_path(m)] = None

    # fence 2: no new macros or notation
    paths = [to_path(m) for m in modified + added]
    diff = git('diff', '-U0', base, '--', *paths) if paths else ''
    new_syntax = [l[:160] for l in diff.splitlines() if NEW_SYNTAX.match(l)]
    report['fence_new_syntax'] = new_syntax[:20]

    # a deleted module must not be imported by any remaining file
    if removed:
        rset = set(removed)
        still = []
        for dp, dn, fn in os.walk(C.SRC):
            for f in fn:
                if f.endswith('.lean'):
                    p = os.path.join(dp, f)
                    with open(p, encoding='utf-8') as fh:
                        head = fh.read(20000)
                    hit = [i for i in IMPORT.findall(head) if i in rset]
                    if hit:
                        still.append((to_module(os.path.relpath(p, C.PROOF)), hit[0]))
        if still:
            report['problems'].append(f'{len(still)} remaining files still import deleted modules, e.g. {still[:3]}')

    # compile, with propagation to users of changed interfaces
    time_cache = C.load_json(TIME_CACHE, {}) or {}
    todo = order_by_imports(modified + added)
    compiled, ifaces = {}, {}
    time_before = time_after = 0.0
    breaking_ids = {}
    news, olds = {}, {}
    rounds = 0
    handled_users = set()
    while todo:
        rounds += 1
        for m in todo:
            r = compile_module(m, new_dir, overlays=[new_dir], threads=a.threads, mem_gb=a.mem_gb, quiet=True)
            compiled[m] = r
            print(f"  compiled {m}: ok={r['ok']} time={r.get('time_s')}s rss={r.get('max_rss_mb')}MB", flush=True)
            if not r['ok']:
                report['problems'].append(f"{m} does not compile: {r.get('messages_tail', r.get('error', ''))[-600:]}")
                continue
            if r.get('mentions_sorry'):
                report['problems'].append(f'{m}: compiler output mentions sorry')
            time_after += r['time_s']
            old_olean = C.current_olean(m)
            if os.path.exists(old_olean) and not a.no_time:
                # time the accepted version of the same file on this machine (cached per file content)
                try:
                    old_text = git('show', f'{base}:{to_path(m)}')
                    key = f'w:{m}:{sha(old_text)}'
                    if key not in time_cache:
                        p = C.module_path(m, oldsrc)
                        os.makedirs(os.path.dirname(p), exist_ok=True)
                        with open(p, 'w', encoding='utf-8') as fh:
                            fh.write(old_text)
                        ro = compile_module(m, old_dir, src=oldsrc, threads=a.threads, mem_gb=a.mem_gb, quiet=True)
                        if ro['ok']:
                            time_cache[key] = ro['time_s']
                            os.makedirs(os.path.dirname(TIME_CACHE), exist_ok=True)
                            json.dump(time_cache, open(TIME_CACHE, 'w'), indent=0)
                        else:
                            report['notes'].append(f'accepted version of {m} did not compile here; time comparison incomplete')
                    time_before += time_cache.get(key, 0.0)
                except subprocess.CalledProcessError:
                    pass                                  # file is new relative to the base
            res, old, new = IFACE.check_module(m, new_dir, old_path=old_olean)
            ifaces[m] = res; news[m] = new; olds[m] = old
            for nm in res['breaking'] + res['aux_to_check']:
                if nm in old:
                    breaking_ids[old[nm]['id']] = nm
        todo = []
        # declarations of deleted modules are gone too
        if rounds == 1 and removed:
            pairs = [(m, C.current_olean(m)) for m in removed if os.path.exists(C.current_olean(m))]
            for i in range(0, len(pairs), 2000):
                for m, info in C.parse_consts(C.moddump(pairs[i:i + 2000])).items():
                    for nm, rec in info['decls'].items():
                        breaking_ids[rec['id']] = nm
        if breaking_ids:
            users = users_of(breaking_ids.keys(), set(compiled) | set(removed), overlay_mods, overlay_removed)
            users = {m: v for m, v in users.items() if m not in handled_users}
            report['users_of_changed'] = {m: v[:5] for m, v in list(users.items())[:50]}
            report['users_of_changed_count'] = len(users)
            if users and a.propagate and len(users) <= a.max_propagate:
                todo = order_by_imports(sorted(users))
                handled_users |= set(todo)
                print(f'  {len(todo)} modules use what changed; recompiling them')
            elif users:
                report['incomplete'] = (f'{len(users)} modules use declarations that changed or disappeared; '
                                        f'they must be recompiled (use --propagate, or a larger machine)')
            breaking_ids = {} if todo else breaking_ids

    report['compiled'] = {m: {k: r.get(k) for k in ('ok', 'time_s', 'cpu_s', 'wall_s', 'max_rss_mb')} for m, r in compiled.items()}
    report['interface'] = {m: {k: (v if not isinstance(v, list) else v[:20]) for k, v in r.items()} for m, r in ifaces.items()}

    # tables for the new state: overlay rows of untouched modules + rows of what was just compiled
    ok_mods = [m for m, r in compiled.items() if r['ok']]
    all_removed = sorted((overlay_removed | set(removed)) - set(ok_mods))
    patch_consts = os.path.join(work, 'consts.tsv')
    patch_decls = os.path.join(work, 'decls.tsv')
    replaced = set(ok_mods) | set(all_removed)
    new_ranges = {}
    with open(patch_consts, 'wb') as fh:
        overlay_consts = os.path.join(C.DATA_OVERLAY, 'consts.tsv')
        if os.path.exists(overlay_consts):
            for m, lines in table_blocks(overlay_consts):
                if m not in replaced:
                    fh.writelines(lines)
        if ok_mods:
            fh.write(b'\n'.join(C.moddump([(m, compiled[m]['olean']) for m in ok_mods])))
            fh.write(b'\n')
    with open(patch_decls, 'w', encoding='utf-8') as fh:
        overlay_decls = os.path.join(C.DATA_OVERLAY, 'decls.tsv')
        if os.path.exists(overlay_decls):
            with open(overlay_decls, encoding='utf-8') as oh:
                for line in oh:
                    if line.split('\t', 1)[0] not in replaced:
                        fh.write(line)
        for m in ok_mods:
            d = C.load_json(compiled[m]['ilean'], {}) or {}
            for name, r in (d.get('decls') or {}).items():
                fh.write(f'{m}\t{r[0]}\t{r[1]}\t{r[2]}\t{r[3]}\t{name}\n')
                new_ranges[(m, name)] = (r[0], r[1], r[2], r[3])

    # validity of what was compiled
    for m in ok_mods:
        for nm, rec in news.get(m, {}).items():
            if rec['kind'] == 'ax':
                report['problems'].append(f'{m} declares an axiom: {nm}')
            for d in rec['tdeps'] + rec['vdeps']:
                if d in C.FORBIDDEN:
                    report['problems'].append(f'{nm} uses {C.FORBIDDEN[d]}')

    summary = None
    if not report['problems'] and 'incomplete' not in report:
        try:
            summary = CONE.compute(C.DATA_BASE, C.SRC, work, patch_consts, patch_decls, all_removed, verbose=False,
                                   src_override=src_override)
        except RuntimeError as e:
            report['problems'].append(str(e))
    if summary and base_summary and before:
        if summary['target_statement_hashes'] != base_summary['target_statement_hashes']:
            report['problems'].append('the statements of the target theorems changed')
        if summary['axioms_declared']:
            report['problems'].append(f"axioms declared: {summary['axioms_declared'][:5]}")
        if summary['forbidden_uses']:
            report['problems'].append(f"forbidden declarations used: {summary['forbidden_uses'][:5]}")
        dials = {}
        for key in ('source_tokens', 'written_out_size'):
            b, n = before[key], summary['cone'][key]
            dials[key] = {'before': b, 'after': n, 'change': n - b}
        dials['time_cpu_s'] = {'before': round(time_before, 1), 'after': round(time_after, 1),
                               'change': round(time_after - time_before, 1),
                               'note': 'recompiled files only; elaboration and checking, imports excluded'}
        dials['cone_declarations'] = {'before': None, 'after': summary['cone']['declarations']}
        report['dials'] = dials

    # fence 1: size cap on declarations that were added or changed
    caps = C.load_json(os.path.join(a.baseline, 'caps.json'))
    over = []
    if caps:
        for m, res in ifaces.items():
            for nm in res['added'] + res['proof_changed'] + res['body_changed'] + res['statement_changed']:
                rec = news[m].get(nm)
                if rec is None:
                    continue
                w = rec['tsize'] + rec['vsize']
                tk = decl_tokens(m, nm, new_ranges)
                old_rec = olds[m].get(nm)
                if old_rec is not None:
                    # an existing declaration may stay over the cap as long as it did not grow
                    if w > caps['written_out'] and w > old_rec['tsize'] + old_rec['vsize']:
                        over.append({'module': m, 'name': nm, 'written_out': w, 'source_tokens': tk})
                elif w > caps['written_out'] or (tk is not None and tk > caps['source_tokens']):
                    over.append({'module': m, 'name': nm, 'written_out': w, 'source_tokens': tk})
    report['fence_size_cap'] = {'caps': caps, 'over': over[:20], 'count': len(over)}

    # what recording this change would put into the accepted state
    report['plan'] = {
        'base_commit': base_commit,
        'modules': ok_mods,
        'removed': all_removed,
        'consts': patch_consts,
        'decls': patch_decls,
        'oleans': {m: compiled[m]['olean'] for m in ok_mods},
        'ileans': {m: compiled[m]['ilean'] for m in ok_mods},
    }

    # verdict
    if report['problems']:
        verdict = 'invalid'
    elif 'incomplete' in report:
        verdict = 'incomplete'
    elif not (summary and base_summary and before):
        verdict = 'incomplete'
        report['incomplete'] = 'no baseline summary to compare with (run tools/cone.py and copy summary.json to baseline/)'
    else:
        d = report['dials']
        tok, wri = d['source_tokens']['change'], d['written_out_size']['change']
        up = []
        if tok > 0:
            if wri <= -EXCHANGE_NODES_PER_TOKEN * tok:
                report['exchange'] = (f'source +{tok} tokens allowed: written-out size fell by {-wri} nodes, '
                                      f'{-wri // tok} per token added (at least {EXCHANGE_NODES_PER_TOKEN} required)')
            else:
                up.append('source_tokens')
        if wri > 0:
            up.append('written_out_size')
        tb, ta = d['time_cpu_s']['before'], d['time_cpu_s']['after']
        if not a.no_time and ta > tb * (1 + TIME_TOLERANCE) + TIME_SLACK_S:
            up.append('time')
        down = [k for k in ('source_tokens', 'written_out_size') if d[k]['change'] < 0]
        fences = []
        if new_syntax:
            fences.append('new macros or notation')
        if over:
            fences.append('declaration over the size cap')
        if up or fences:
            verdict = 'review'
            report['review_reasons'] = [f'{k} went up' for k in up] + fences
        else:
            verdict = 'accept'
            report['progress'] = down
            if report.get('exchange'):
                report['notes'].append(report['exchange'])
    report['verdict'] = verdict
    report['seconds'] = round(time.time() - t0)
    json.dump(report, open(os.path.join(work, 'verdict.json'), 'w'), indent=1)

    print()
    print(f'VERDICT: {verdict}')
    for p in report['problems'][:10]:
        print('  problem:', p[:400])
    if 'incomplete' in report:
        print('  ', report['incomplete'])
    for k, v in (report.get('dials') or {}).items():
        print(f'  {k}: {v}')
    for r in report.get('review_reasons', []):
        print('  review:', r)
    if report.get('progress'):
        print('  went down:', ', '.join(report['progress']))
    if report.get('exchange') and verdict == 'accept':
        print('  trade:', report['exchange'])
    print(f"  details: {os.path.join(work, 'verdict.json')}")
    sys.exit({'accept': 0, 'review': 3, 'incomplete': 4, 'invalid': 1}[verdict])


if __name__ == '__main__':
    main()
