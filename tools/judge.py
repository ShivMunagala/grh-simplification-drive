#!/usr/bin/env python3
"""Judge the working tree against a base version.

  tools/judge.py [--base upstream] [--work build/judge] [--propagate] [--no-time]

What it does, all on this machine:

 1. Lists the source files in proof/ changed, added or deleted since --base (by default the
    unmodified archive), whether or not the changes are committed yet.
 2. Compiles each changed or added file on its own against the compiled base (sandboxed), and,
    for timing, the base version of each changed file as well.
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
import argparse, collections, json, os, re, shutil, subprocess, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C
import cone as CONE
import iface as IFACE
from compile_one import compile_module

NEW_SYNTAX = re.compile(r'^\+(?!\+\+).*\b(macro|macro_rules|syntax|notation|infix|infixl|infixr|prefix|postfix|'
                        r'elab|elab_rules|declare_syntax_cat|binder_predicate)\b')
IMPORT = re.compile(r"^\s*(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+)?([^\s]+)", re.M)
TIME_TOLERANCE = 0.05


def git(*args):
    """git in the proof repository (proof/), whose tag `upstream` is the unmodified archive."""
    return subprocess.run(['git', '-C', C.PROOF] + list(args), stdout=subprocess.PIPE, check=True).stdout.decode()


def to_module(path):
    """`src/A/B.lean` (relative to proof/) -> `A.B`."""
    rel = os.path.relpath(os.path.join(C.PROOF, path), C.SRC)
    return rel[:-5].replace(os.sep, '.')


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


def users_of(ids, exclude_modules):
    """Scan the base table: which declarations (by module) mention any of the given ids?"""
    want = {str(i).encode() for i in ids}
    users = collections.defaultdict(list)
    cur, keep = None, True
    for line in CONE.zlines(os.path.join(C.DATA_BASE, 'consts.tsv.zst')):
        tag = line[:1]
        if tag == b'M':
            cur = line.split(b'\t')[1].decode()
            keep = cur not in exclude_modules
        elif tag == b'C' and keep:
            f = line.rstrip(b'\n').split(b'\t', 9)
            if len(f) != 10:
                continue
            hit = (f[7] and not want.isdisjoint(f[7].split(b' '))) or (f[8] and not want.isdisjoint(f[8].split(b' ')))
            if hit:
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--base', default=C.UPSTREAM_TAG,
                    help='commit or tag in proof/ to compare with (default: the unmodified archive)')
    ap.add_argument('--work', default=os.path.join(C.ROOT, 'build', 'judge'))
    ap.add_argument('--baseline', default=os.path.join(C.ROOT, 'baseline'))
    ap.add_argument('--propagate', action='store_true', help='also recompile modules that use what changed')
    ap.add_argument('--no-time', action='store_true', help='skip recompiling base versions for timing')
    ap.add_argument('--threads', type=int, default=1)
    ap.add_argument('--mem-gb', type=float, default=8.0)
    ap.add_argument('--max-propagate', type=int, default=50)
    a = ap.parse_args()

    t0 = time.time()
    work = os.path.abspath(a.work)
    shutil.rmtree(work, ignore_errors=True)
    new_dir, old_dir, oldsrc = (os.path.join(work, d) for d in ('new', 'old', 'oldsrc'))
    for d in (new_dir, old_dir, oldsrc):
        os.makedirs(d)
    report = {'base': a.base, 'problems': [], 'notes': []}

    modified, added, removed = changed_files(a.base)
    report['modified'], report['added'], report['removed'] = modified, added, removed
    print(f'changed: {len(modified)} modified, {len(added)} added, {len(removed)} deleted')
    if not (modified or added or removed):
        print('nothing changed')
        return

    # fence 2: no new macros or notation
    new_syntax = [l[:160] for l in git('diff', '-U0', a.base, '--', 'src').splitlines() if NEW_SYNTAX.match(l)]
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
    todo = order_by_imports(modified + added)
    compiled, ifaces = {}, {}
    time_before = time_after = 0.0
    breaking_ids, breaking_names = {}, []
    olds, news = {}, {}
    rounds = 0
    handled_users = set()
    while todo:
        rounds += 1
        for m in todo:
            r = compile_module(m, new_dir, overlays=[new_dir], threads=a.threads, mem_gb=a.mem_gb, quiet=True)
            compiled[m] = r
            print(f"  compiled {m}: ok={r['ok']} cpu={r.get('cpu_s')}s rss={r.get('max_rss_mb')}MB")
            if not r['ok']:
                report['problems'].append(f"{m} does not compile: {r.get('messages_tail', r.get('error', ''))[-600:]}")
                continue
            if r.get('mentions_sorry'):
                report['problems'].append(f'{m}: compiler output mentions sorry')
            time_after += r['cpu_s']
            had_old = os.path.exists(C.module_path(m, C.COMPILED, '.olean'))
            if had_old and not a.no_time:
                # time the base version of the same file on this machine, for a fair comparison
                try:
                    old_text = git('show', f'{a.base}:src/' + m.replace('.', '/') + '.lean')
                    p = C.module_path(m, oldsrc)
                    os.makedirs(os.path.dirname(p), exist_ok=True)
                    with open(p, 'w', encoding='utf-8') as fh:
                        fh.write(old_text)
                    ro = compile_module(m, old_dir, src=oldsrc, threads=a.threads, mem_gb=a.mem_gb, quiet=True)
                    if ro['ok']:
                        time_before += ro['cpu_s']
                    else:
                        report['notes'].append(f'base version of {m} did not compile here; time comparison incomplete')
                except subprocess.CalledProcessError:
                    pass                                  # file is new relative to base
            res, old, new = IFACE.check_module(m, new_dir)
            ifaces[m] = res; olds[m] = old; news[m] = new
            for nm in res['breaking'] + res['aux_to_check']:
                if nm in old:
                    breaking_ids[old[nm]['id']] = nm
            breaking_names += res['breaking']
        todo = []
        # declarations of deleted modules are gone too
        if rounds == 1 and removed:
            pairs = [(m, C.module_path(m, C.COMPILED, '.olean')) for m in removed
                     if os.path.exists(C.module_path(m, C.COMPILED, '.olean'))]
            for i in range(0, len(pairs), 2000):
                for m, info in C.parse_consts(C.moddump(pairs[i:i + 2000])).items():
                    for nm, rec in info['decls'].items():
                        breaking_ids[rec['id']] = nm
        if breaking_ids:
            users = users_of(breaking_ids.keys(), set(compiled) | set(removed))
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

    report['compiled'] = {m: {k: r.get(k) for k in ('ok', 'cpu_s', 'wall_s', 'max_rss_mb')} for m, r in compiled.items()}
    report['interface'] = {m: {k: (v if not isinstance(v, list) else v[:20]) for k, v in r.items()} for m, r in ifaces.items()}

    # tables for the recompiled modules
    ok_mods = [m for m, r in compiled.items() if r['ok']]
    patch_consts = os.path.join(work, 'consts.tsv')
    patch_decls = os.path.join(work, 'decls.tsv')
    removed_file = os.path.join(work, 'removed.txt')
    with open(patch_consts, 'wb') as fh:
        if ok_mods:
            fh.write(b'\n'.join(C.moddump([(m, compiled[m]['olean']) for m in ok_mods])))
    new_ranges = {}
    with open(patch_decls, 'w', encoding='utf-8') as fh:
        for m in ok_mods:
            d = C.load_json(compiled[m]['ilean'], {}) or {}
            for name, r in (d.get('decls') or {}).items():
                fh.write(f'{m}\t{r[0]}\t{r[1]}\t{r[2]}\t{r[3]}\t{name}\n')
                new_ranges[(m, name)] = (r[0], r[1], r[2], r[3])
    with open(removed_file, 'w') as fh:
        fh.write('\n'.join(removed))

    # validity of what was compiled
    for m in ok_mods:
        for nm, rec in news.get(m, {}).items():
            if rec['kind'] == 'ax':
                report['problems'].append(f'{m} declares an axiom: {nm}')
            for d in rec['tdeps'] + rec['vdeps']:
                if d in C.FORBIDDEN:
                    report['problems'].append(f'{nm} uses {C.FORBIDDEN[d]}')

    base_summary = C.load_json(os.path.join(a.baseline, 'summary.json'))
    summary = None
    if not report['problems'] and 'incomplete' not in report:
        try:
            summary = CONE.compute(C.DATA_BASE, C.SRC, work, patch_consts, patch_decls, removed, verbose=False)
        except RuntimeError as e:
            report['problems'].append(str(e))
    if summary and base_summary:
        if summary['target_statement_hashes'] != base_summary['target_statement_hashes']:
            report['problems'].append('the statements of the target theorems changed')
        if summary['axioms_declared']:
            report['problems'].append(f"axioms declared: {summary['axioms_declared'][:5]}")
        if summary['forbidden_uses']:
            report['problems'].append(f"forbidden declarations used: {summary['forbidden_uses'][:5]}")
        dials = {}
        for key in ('source_tokens', 'written_out_size'):
            b, n = base_summary['cone'][key], summary['cone'][key]
            dials[key] = {'before': b, 'after': n, 'change': n - b}
        dials['time_cpu_s'] = {'before': round(time_before, 1), 'after': round(time_after, 1),
                               'change': round(time_after - time_before, 1),
                               'note': 'recompiled files only, same machine'}
        dials['cone_declarations'] = {'before': base_summary['cone']['declarations'],
                                      'after': summary['cone']['declarations']}
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
                if w > caps['written_out'] or (tk is not None and tk > caps['source_tokens']):
                    over.append({'module': m, 'name': nm, 'written_out': w, 'source_tokens': tk})
    report['fence_size_cap'] = {'caps': caps, 'over': over[:20], 'count': len(over)}

    # verdict
    if report['problems']:
        verdict = 'invalid'
    elif 'incomplete' in report:
        verdict = 'incomplete'
    elif not (summary and base_summary):
        verdict = 'incomplete'
        report['incomplete'] = 'no baseline summary to compare with (run tools/cone.py and copy summary.json to baseline/)'
    else:
        d = report['dials']
        up = [k for k in ('source_tokens', 'written_out_size') if d[k]['change'] > 0]
        tb, ta = d['time_cpu_s']['before'], d['time_cpu_s']['after']
        if not a.no_time and ta > tb * (1 + TIME_TOLERANCE) + 1.0:
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
    print(f"  details: {os.path.join(work, 'verdict.json')}")
    sys.exit({'accept': 0, 'review': 3, 'incomplete': 4, 'invalid': 1}[verdict])


if __name__ == '__main__':
    main()
