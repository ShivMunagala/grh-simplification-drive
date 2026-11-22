#!/usr/bin/env python3
"""Quick check of an edit to one file, before bothering the judge.

  tools/try_change.py Development.Some.Module

Compiles the file as it is now in proof/ against the accepted state, then reports:

  * whether it compiles (errors are printed);
  * whether it still exposes the same statements and definitions (the equivalence check);
  * for the whole file, old and new: source tokens, written-out size, compile time;
  * for each declaration whose proof or body changed: written-out size before and after
    (including the auxiliary declarations the compiler generates for it).

The last line is `PRECHECK: pass` if the edit is valid, changes no existing interface, does not slow
the file down beyond tolerance, lowers at least one size and raises neither. One trade is allowed:
source tokens may rise if the written-out size falls by at least 1,000 nodes per token added. New
helper declarations are allowed and are listed. That is what the judge will require; the judge
itself then recomputes the dials over the whole cone.

Takes a minute or more per run: one compile of the file (two the first time, to time the old version).
"""
import argparse, json, os, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C
import cone as CONE
import iface as IFACE
from compile_one import compile_module
from judge import git, to_path, sha, TIME_CACHE, TIME_TOLERANCE, TIME_SLACK_S, EXCHANGE_NODES_PER_TOKEN


def group_sizes(decls):
    """Written-out size per named declaration, with compiler-generated auxiliaries rolled into it."""
    names = [n for n in decls if not IFACE.AUX.search(n)]
    out = {n: decls[n]['tsize'] + decls[n]['vsize'] for n in names}
    for n, rec in decls.items():
        if n in out:
            continue
        p = n
        while p not in out and '.' in p:
            p = p.rsplit('.', 1)[0]
        if p in out:
            out[p] += rec['tsize'] + rec['vsize']
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('module')
    ap.add_argument('--mem-gb', type=float, default=8.0)
    ap.add_argument('--timeout', type=int, default=3600)
    a = ap.parse_args()
    m = a.module
    state = C.accepted_state()
    base = state['proof_commit'] if state else C.UPSTREAM_TAG
    work = os.path.join(C.ROOT, 'build', 'try', m)
    new_dir, old_dir, oldsrc = (os.path.join(work, d) for d in ('new', 'old', 'oldsrc'))

    r = compile_module(m, new_dir, overlays=[new_dir], mem_gb=a.mem_gb, timeout=a.timeout, quiet=True)
    if not r['ok']:
        print('DOES NOT COMPILE')
        print(r.get('messages_tail') or r.get('error') or '')
        print('PRECHECK: fail (does not compile)')
        sys.exit(1)

    old_text = git('show', f'{base}:{to_path(m)}')
    with open(C.module_path(m), encoding='utf-8') as fh:
        new_text = fh.read()
    cache = C.load_json(TIME_CACHE, {}) or {}
    key = f'w:{m}:{sha(old_text)}'
    if key not in cache:
        p = C.module_path(m, oldsrc)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        with open(p, 'w', encoding='utf-8') as fh:
            fh.write(old_text)
        ro = compile_module(m, old_dir, src=oldsrc, mem_gb=a.mem_gb, timeout=a.timeout, quiet=True)
        if ro['ok']:
            cache = C.load_json(TIME_CACHE, {}) or {}
            cache[key] = ro['time_s']
            os.makedirs(os.path.dirname(TIME_CACHE), exist_ok=True)
            json.dump(cache, open(TIME_CACHE, 'w'), indent=0)
    t_old, t_new = cache.get(key), r['time_s']

    res, old, new = IFACE.check_module(m, new_dir)
    g_old, g_new = group_sizes(old), group_sizes(new)
    w_old, w_new = sum(g_old.values()), sum(g_new.values())
    k_old, k_new = CONE.count_tokens(old_text), CONE.count_tokens(new_text)

    reasons = []
    if not res['compatible']:
        what = res['breaking'][:5] or [f'{k}: {a} -> {b} entries' for k, (a, b) in res.get('ext_changed', {}).items()] \
            or [f'imports changed: +{res.get("imports_added")} -{res.get("imports_removed")}'
                if res.get('imports_added') or res.get('imports_removed')
                else 'namespaces removed: ' + ', '.join(res.get('ns_removed', []))]
        reasons.append('interface changed: ' + ', '.join(what))
    if res.get('signature_changed'):
        print('  same statement but different argument names, explicit/implicit arguments or universe order: '
              + ', '.join(res['signature_changed'][:5]))
    if res.get('ns_added'):
        print('  registers new namespaces (the judge decides whether that matters): ' + ', '.join(res['ns_added']))
    named_added = [n for n in res['added'] if not IFACE.AUX.search(n)]
    if k_new > k_old:
        # the one agreed trade: tokens may rise if the written-out size falls enough per token added
        if w_old - w_new >= EXCHANGE_NODES_PER_TOKEN * (k_new - k_old):
            print(f'trade: +{k_new - k_old} tokens for -{w_old - w_new} nodes '
                  f'({(w_old - w_new) // (k_new - k_old)} per token; at least {EXCHANGE_NODES_PER_TOKEN} required)')
        else:
            reasons.append(f'source tokens went up ({k_old} -> {k_new}) without saving at least '
                           f'{EXCHANGE_NODES_PER_TOKEN} written-out nodes per token added')
    if w_new > w_old:
        reasons.append(f'written-out size went up ({w_old} -> {w_new})')
    if t_old is not None and t_new > t_old * (1 + TIME_TOLERANCE) + TIME_SLACK_S:
        reasons.append(f'compile time went up ({t_old:.1f}s -> {t_new:.1f}s)')
    if r.get('mentions_sorry'):
        reasons.append('compiler output mentions sorry')
    if k_new == k_old and w_new == w_old:
        reasons.append('nothing got smaller')

    print(f'file: source tokens {k_old} -> {k_new} ({k_new - k_old:+d}); written-out {w_old} -> {w_new} '
          f'({w_new - w_old:+d}); compile time {t_old if t_old is not None else "?"}s -> {t_new}s; '
          f'peak memory {r["max_rss_mb"]} MB')
    if named_added:
        print('new declarations: ' + ', '.join(named_added[:10]))
    changed = sorted(set(n for n in g_old if g_old.get(n) != g_new.get(n)) | set(n for n in g_new if n not in g_old))
    for n in changed[:30]:
        print(f'  {n}: written-out {g_old.get(n, 0)} -> {g_new.get(n, 0)}')
    if reasons:
        print('PRECHECK: fail (' + '; '.join(reasons) + ')')
        sys.exit(2)
    print('PRECHECK: pass')


if __name__ == '__main__':
    main()
