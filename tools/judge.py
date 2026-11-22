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
    # core.quotePath=false: paths with non-ASCII characters are printed as they are, not escaped
    return subprocess.run(['git', '-C', C.PROOF, '-c', 'core.quotePath=false'] + list(args),
                          stdout=subprocess.PIPE, check=True).stdout.decode()


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


def users_of(ids, exclude_modules, overlay_mods, overlay_removed, used=None):
    """Which declarations of the accepted state (by module) mention any of the given ids?
    If `used` is a set, the ids that are mentioned are added to it."""
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
                    if used is not None:
                        used.update(int(x) for x in (want & (set(f[7].split(b' ')) | set(f[8].split(b' ')))))
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


class BaseSource:
    """Read source files from a commit of the proof repository, through one long-lived git process."""

    def __init__(self, commit):
        self.commit = commit
        self.p = subprocess.Popen(['git', '-C', C.PROOF, 'cat-file', '--batch'],
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE)

    def read(self, module):
        self.p.stdin.write(f'{self.commit}:{to_path(module)}\n'.encode())
        self.p.stdin.flush()
        header = self.p.stdout.readline().split()
        if len(header) < 3:
            return None
        size = int(header[2])
        data = self.p.stdout.read(size)
        self.p.stdout.read(1)
        return data.decode('utf-8', 'replace')

    def close(self):
        try:
            self.p.stdin.close()
            self.p.wait(timeout=10)
        except Exception:
            self.p.kill()


def sha(text):
    return hashlib.sha256(text if isinstance(text, bytes) else text.encode('utf-8')).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--base', default=None,
                    help='commit in proof/ to compare with (default: the accepted commit, or the unmodified archive)')
    ap.add_argument('--only', default=None, help='comma-separated modules: judge only these changed files')
    ap.add_argument('--only-file', default=None, help='the same, as a file with one module per line')
    ap.add_argument('--work', default=os.path.join(C.ROOT, 'build', 'judge'))
    ap.add_argument('--baseline', default=os.path.join(C.ROOT, 'baseline'))
    ap.add_argument('--propagate', action='store_true', help='also recompile modules that use what changed')
    ap.add_argument('--no-time', action='store_true', help='skip timing of the accepted versions')
    ap.add_argument('--precompiled', default=None,
                    help='directory holding new/<Module>.olean and .ilean compiled elsewhere (tools/batch_compile.py '
                         'on a rented machine). Nothing is compiled here; interfaces and dials are still checked here.')
    ap.add_argument('--drop-used', action='store_true',
                    help='with --precompiled: leave out modules whose change removes or alters something another '
                         'module still mentions (they are listed in <work>/left_out.txt), and judge the rest')
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
    if a.only or a.only_file:
        only = set(a.only.split(',')) if a.only else set()
        if a.only_file:
            with open(a.only_file) as fh:
                only |= {l.strip() for l in fh if l.strip()}
        skipped = [m for m in modified + added + removed if m not in only]
        if skipped:
            report['notes'].append(f'{len(skipped)} other changed files ignored because of --only')
        modified, added, removed = ([m for m in l if m in only] for l in (modified, added, removed))
    report['modified'], report['added'], report['removed'] = modified, added, removed
    print(f'changed: {len(modified)} modified, {len(added)} added, {len(removed)} deleted')
    if not (modified or added or removed):
        print('nothing changed')
        return
    # Snapshot the judged files now. Everything else is read from the accepted commit, never from
    # the working tree, where other people may be editing while this runs.
    report['changed_hashes'] = {}
    snapshot = {}
    for m in modified + added:
        with open(C.module_path(m), 'rb') as fh:
            data = fh.read()
        report['changed_hashes'][to_path(m)] = sha(data)
        snapshot[m] = data.decode('utf-8', 'replace')
    for m in removed:
        report['changed_hashes'][to_path(m)] = None

    # fence 2: no new macros or notation
    paths = [to_path(m) for m in modified + added]
    diff = ''.join(git('diff', '-U0', base, '--', *paths[i:i + 400]) for i in range(0, len(paths), 400))
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

    # modules compiled elsewhere: read both versions of all of them in a few passes
    bulk = None
    pre_times = {}
    if a.precompiled:
        pre_new = os.path.join(os.path.abspath(a.precompiled), 'new')
        # times measured where the modules were compiled; only modules timed both ways are compared
        pre_times = {m: t for m, t in (C.load_json(os.path.join(os.path.abspath(a.precompiled), 'times.json'), {})
                                       or {}).items()
                     if t.get('before') is not None and t.get('after') is not None}
        if not any(m in pre_times for m in modified):
            a.no_time = True               # no before/after times came with the compiled modules
        pairs = []
        for m in modified + added:
            for tag, path in (('@old', C.current_olean(m)), ('@new', C.module_path(m, pre_new, '.olean'))):
                if os.path.exists(path):
                    pairs.append((m + tag, path))
        bulk = {}
        for i in range(0, len(pairs), 4000):
            bulk.update(C.parse_consts(C.moddump(pairs[i:i + 4000])))
        timed = sum(1 for m in modified if m in pre_times)
        report['notes'].append(f'{len(modified) + len(added)} modules were compiled on another machine; '
                               'interfaces and dials were checked here'
                               + (', time was not compared' if a.no_time else
                                  f', time was measured there before and after on {timed} of them; the time dial '
                                  'counts only those'))

    # compile, with propagation to users of changed interfaces
    time_cache = C.load_json(TIME_CACHE, {}) or {}
    todo = order_by_imports(modified + added)
    compiled, ifaces = {}, {}
    time_before = time_after = 0.0
    breaking_ids = {}
    breaking_owner = {}
    news, olds = {}, {}
    rounds = 0
    handled_users = set()
    while todo:
        rounds += 1
        for m in todo:
            if bulk is not None and (m + '@new') in bulk:
                r = {'module': m, 'ok': True, 'time_s': pre_times[m]['after'] if m in pre_times else 0.0,
                     'mentions_sorry': False,
                     'olean': C.module_path(m, pre_new, '.olean'), 'ilean': C.module_path(m, pre_new, '.ilean')}
            elif bulk is not None and m in modified + added:
                r = {'module': m, 'ok': False, 'error': 'no compiled module was supplied for it'}
            else:
                r = compile_module(m, new_dir, overlays=[new_dir], threads=a.threads, mem_gb=a.mem_gb, quiet=True)
                print(f"  compiled {m}: ok={r['ok']} time={r.get('time_s')}s rss={r.get('max_rss_mb')}MB", flush=True)
            compiled[m] = r
            if not r['ok']:
                report['problems'].append(f"{m} does not compile: {r.get('messages_tail', r.get('error', ''))[-600:]}")
                continue
            if r.get('mentions_sorry'):
                report['problems'].append(f'{m}: compiler output mentions sorry')
            time_after += r['time_s']
            old_olean = C.current_olean(m)
            if bulk is not None and not a.no_time and m in pre_times:
                time_before += pre_times[m]['before']
            elif bulk is None and os.path.exists(old_olean) and not a.no_time:
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
            if bulk is not None and (m + '@new') in bulk:
                res = IFACE.compare_modules(bulk.get(m + '@old'), bulk[m + '@new'])
                old = (bulk.get(m + '@old') or {'decls': {}})['decls']
                new = bulk[m + '@new']['decls']
                res['module'] = m
            else:
                res, old, new = IFACE.check_module(m, new_dir, old_path=old_olean)
            ifaces[m] = res; news[m] = new; olds[m] = old
            for nm in res['breaking'] + res['aux_to_check']:
                if nm in old:
                    breaking_ids[old[nm]['id']] = nm
                    breaking_owner[old[nm]['id']] = m
        todo = []
        # A declaration that left one judged module and appears, unchanged, in another judged module that
        # the first one imports has only moved: every file that could see it before still can.
        added_in = {}
        for m2, res2 in ifaces.items():
            for nm in res2['added']:
                added_in[nm] = m2
        for m2, res2 in ifaces.items():
            if bulk is not None and (m2 + '@new') in bulk:
                direct = set(bulk[m2 + '@new'].get('imports') or ())
            else:
                direct = set(imports_of(m2))
            moved = []
            for nm in res2['removed']:
                y = added_in.get(nm)
                if not y or y == m2 or y not in direct:
                    continue
                o, n = olds[m2][nm], news[y][nm]
                same = (o['kind'] == n['kind'] and o['thash'] == n['thash'] and o['tsize'] == n['tsize']
                        and o.get('st') == n.get('st') and o.get('lp') == n.get('lp')
                        and (o['kind'] == 'thm' or (o['vhash'] == n['vhash'] and o['vsize'] == n['vsize']
                                                    and o.get('sv') == n.get('sv'))))
                if same:
                    moved.append(nm)
            if moved:
                res2['moved'] = moved
                res2['removed'] = [x for x in res2['removed'] if x not in moved]
                res2['breaking'] = [x for x in res2['breaking'] if x not in moved]
                res2['compatible'] = not (res2['breaking'] or res2.get('ext_changed') or res2.get('ns_removed')
                                          or res2.get('imports_added') or res2.get('imports_removed'))
                for nm in moved:
                    breaking_ids.pop(olds[m2][nm]['id'], None)
                    breaking_owner.pop(olds[m2][nm]['id'], None)
                report['notes'].append(f'{len(moved)} declaration(s) moved from {m2} to a module it imports: '
                                       + ', '.join(moved[:5]))
        # declarations of deleted modules are gone too
        if rounds == 1 and removed:
            pairs = [(m, C.current_olean(m)) for m in removed if os.path.exists(C.current_olean(m))]
            for i in range(0, len(pairs), 2000):
                for m, info in C.parse_consts(C.moddump(pairs[i:i + 2000])).items():
                    for nm, rec in info['decls'].items():
                        breaking_ids[rec['id']] = nm
        if breaking_ids:
            left_out = report.setdefault('left_out', [])
            while True:
                used = set()
                users = users_of(breaking_ids.keys(), set(compiled) | set(removed), overlay_mods, overlay_removed, used)
                users = {m: v for m, v in users.items() if m not in handled_users}
                if bulk is not None:
                    # Modules compiled elsewhere were each compiled against the accepted state, not against
                    # each other: one of them may still mention what another one changed or removed.
                    for m2, decls in news.items():
                        hit = []
                        for nm, rec in decls.items():
                            # (a module's own regenerated helpers keep their names: not a foreign use)
                            ids = [d for d in rec['tdeps'] + rec['vdeps']
                                   if d in breaking_ids and breaking_owner.get(d) != m2]
                            if ids:
                                hit.append(nm)
                                used.update(ids)
                        if hit:
                            users.setdefault(m2, []).extend(hit)
                owners = {breaking_owner[i] for i in used if i in breaking_owner}
                if not (bulk is not None and a.drop_used and users and owners):
                    break
                # Leave those modules as they are in the accepted state, and look again: a module that
                # is no longer part of the change may itself use what another one removes.
                for m in owners:
                    for d in (compiled, ifaces, news, olds, snapshot):
                        d.pop(m, None)
                    report['changed_hashes'].pop(to_path(m), None)
                    left_out.append(m)
                modified[:] = [m for m in modified if m not in owners]
                added[:] = [m for m in added if m not in owners]
                breaking_ids = {i: nm for i, nm in breaking_ids.items() if breaking_owner.get(i) not in owners}
                print(f'  left out {len(owners)} module(s): another module uses what their change removes or alters', flush=True)
                if not breaking_ids:
                    users = {}
                    break
            if left_out:
                with open(os.path.join(work, 'left_out.txt'), 'w') as fh:
                    fh.write('\n'.join(to_path(m) for m in left_out) + '\n')
                report['notes'].append(f'{len(left_out)} module(s) were left out because another module uses what their '
                                       'change removes or alters; their files must be restored before committing')
                time_after = sum(pre_times[m]['after'] for m in compiled if m in pre_times)
                time_before = sum(pre_times[m]['before'] for m in compiled if m in pre_times)
            report['changed_or_removed'] = sorted(breaking_ids.values())[:200]
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

    # What the recompiled modules register with Lean. A changed count of attributes, instances and
    # the like, or a namespace that is gone, can change how other modules elaborate without any
    # statement changing. A new namespace matters only if some `open` in the tree can resolve to it.
    registers_changed, ns_added = [], collections.defaultdict(list)
    for m, res in ifaces.items():
        if res.get('ext_changed') or res.get('ns_removed') or res.get('imports_added') or res.get('imports_removed'):
            registers_changed.append({'module': m, 'entries': res.get('ext_changed'), 'namespaces_removed': res.get('ns_removed'),
                                      'imports_added': res.get('imports_added'), 'imports_removed': res.get('imports_removed')})
        for n in res.get('ns_added', []):
            ns_added[n].append(m)
    report['registers_changed'] = registers_changed[:20]
    report['registers_changed_count'] = len(registers_changed)
    report['namespaces_added'] = {}
    ns_reasons = []
    if ns_added:
        import nscheck as NS
        imports, registers = NS.load()
        fresh = {}
        for n, ms in sorted(ns_added.items()):
            seen = NS.seen_by(imports, registers, n)
            new_for = [m for m in ms if m not in seen]
            report['namespaces_added'][n] = {'modules': len(ms), 'not_already_registered_by_an_import': len(new_for)}
            if new_for:
                fresh[n] = new_for
        if fresh:
            hits = NS.open_commands(sorted(fresh))
            risky = {f'{k[0]} {k[1]}': len(v) for k, v in hits.items() if k[2] == 'proper suffix'}
            report['namespaces_added_open_commands'] = {f'{k[0]} {k[1]} ({k[2]})': len(v) for k, v in hits.items()}
            if risky:
                ns_reasons.append(f'new namespaces {sorted(fresh)} can be reached by existing commands: {risky}')
            else:
                report['notes'].append(
                    f'{sorted(fresh)} become registered namespaces; no `open` or `export` in the tree names a '
                    'proper suffix of them, so no existing file can resolve to them')

    report['compiled'] = {m: {k: r.get(k) for k in ('ok', 'time_s', 'cpu_s', 'wall_s', 'max_rss_mb')} for m, r in compiled.items()}
    # per-module detail; for a large batch only the modules where something other than a proof changed
    detail = ifaces if len(ifaces) <= 500 else {
        m: r for m, r in ifaces.items()
        if not r['compatible'] or r['added'] or r['aux_to_check'] or r.get('ext_changed')}
    report['interface'] = {m: {k: (v if not isinstance(v, list) else v[:20]) for k, v in r.items()}
                           for m, r in list(detail.items())[:2000]}
    report['interface_counts'] = {
        'modules': len(ifaces), 'compatible': sum(1 for r in ifaces.values() if r['compatible']),
        'checked_strictly': sum(1 for r in ifaces.values() if r.get('strict')),
        'proofs_changed': sum(len(r['proof_changed']) for r in ifaces.values()),
        'declarations_added': sum(len(r['added']) for r in ifaces.values())}

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
        stored_ranges = {}
        for i in range(0, len(ok_mods), 4000):
            lines = C.moddump([(m, compiled[m]['olean']) for m in ok_mods[i:i + 4000]])
            fh.write(b'\n'.join(lines))
            fh.write(b'\n')
            for m, info in C.parse_consts(lines).items():
                stored_ranges[m] = info.get('ranges') or {}
    # Source ranges come from each module's index file (.ilean), as for the baseline. Some commands
    # leave no entry there (`alias` is one); the declaration would then count as zero tokens. For a
    # declaration that had a range before, or is new, the range stored in the compiled module is used.
    had_range = collections.defaultdict(set)
    judged = set(ok_mods)
    for path in (os.path.join(C.DATA_BASE, 'decls.tsv.zst'), os.path.join(C.DATA_OVERLAY, 'decls.tsv')):
        if judged and os.path.exists(path):
            for line in CONE.zlines(path):
                f = line.rstrip(b'\n').split(b'\t', 5)
                if len(f) == 6 and f[0].decode() in judged:
                    had_range[f[0].decode()].add(f[5].decode('utf-8', 'replace'))
    filled = 0
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
            for name, r in stored_ranges.get(m, {}).items():
                if (m, name) in new_ranges or name not in news.get(m, {}):
                    continue
                if name in had_range[m] or name not in olds.get(m, {}):
                    fh.write(f'{m}\t{r[0]}\t{r[1]}\t{r[2]}\t{r[3]}\t{name}\n')
                    new_ranges[(m, name)] = r
                    filled += 1
    if filled:
        report['notes'].append(f'{filled} declaration(s) have no entry in the index file; their source range was taken '
                               'from the compiled module so that they are still counted')

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
            for m in modified + added:              # the judged files must not have moved under us
                with open(C.module_path(m), 'rb') as fh:
                    if sha(fh.read()) != report['changed_hashes'][to_path(m)]:
                        raise RuntimeError(f'{m} was edited while it was being judged; run the judge again')
            base_source = BaseSource(base_commit)
            summary = CONE.compute(C.DATA_BASE, C.SRC, work, patch_consts, patch_decls, all_removed, verbose=False,
                                   read_source=lambda mod: snapshot[mod] if mod in snapshot else base_source.read(mod))
            base_source.close()
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
                        over.append({'module': m, 'name': nm, 'written_out': w, 'source_tokens': tk, 'existing': True})
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
            # A new helper may be over the cap when it replaces more than it adds: the cone's
            # written-out size must fall by at least the weight of the over-cap new declarations.
            grown = [o for o in over if o.get('existing')]
            added_weight = sum(o['written_out'] for o in over if not o.get('existing'))
            if not grown and wri <= -added_weight:
                report['notes'].append(f'{len(over)} new declaration(s) over the size cap allowed: they weigh '
                                       f'{added_weight} nodes and the cone lost {-wri}')
            else:
                fences.append('declaration over the size cap')
        if registers_changed:
            fences.append(f'{len(registers_changed)} recompiled module(s) import different modules, or register '
                          'different attributes, instances or namespaces, than before')
        fences += ns_reasons
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
    for n, info in (report.get('namespaces_added') or {}).items():
        print(f'  namespace {n}: newly registered by {info["modules"]} module(s), '
              f'{info["not_already_registered_by_an_import"]} of which did not already import one that registers it')
    for note in report.get('notes', [])[:6]:
        print('  note:', note[:300])
    if report.get('progress'):
        print('  went down:', ', '.join(report['progress']))
    if report.get('exchange') and verdict == 'accept':
        print('  trade:', report['exchange'])
    print(f"  details: {os.path.join(work, 'verdict.json')}")
    sys.exit({'accept': 0, 'review': 3, 'incomplete': 4, 'invalid': 1}[verdict])


if __name__ == '__main__':
    main()
