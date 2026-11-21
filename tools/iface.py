#!/usr/bin/env python3
"""The small equivalence check: does a recompiled module still expose what it exposed before?

  tools/iface.py Development.Some.Module --new build/x [--old compiled/lib/lean]

Other modules never look inside a proof; they only see each theorem's statement, and each
definition's statement and body. So if a recompiled module has

  * every declaration the old one had,
  * with the same statement, and
  * for anything that is not a theorem, the same body,

then every already-compiled module that uses it is still a valid proof and needs no rebuild.
New declarations are harmless. Changed or missing ones are listed, so that only the modules
that actually use them need to be looked at.

Auxiliary declarations that the compiler generates inside a proof (`foo._proof_3`, `foo.match_1`,
...) are reported separately: they are normally used only by the declaration they belong to.
"""
import argparse, json, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common as C

AUX = re.compile(r"(\._proof_\d+(?:_\d+)*|\.proof_\d+(?:_\d+)*|\.match_\d+(?:_\d+)*|\._simp_\d+(?:_\d+)*|"
                 r"\.eq_\d+|\.eq_def|\.congr_simp|\._sunfold|"
                 r"\._unsafe_rec|\._unary|\._mutual|\._lambda_\d+|\._closed_\d+|\.splitter|\._auxLemma\.\d+|"
                 r"\._aux_\w+|\.omega_nat|\.hcongr_\d+|\._eq_\d+|\.sizeOf_spec|\.injEq|\.inj|\.noConfusion\w*|"
                 r"\._nativeDecide\w*|\._cstage\d+|\._boxed|\._redArg|\._spec_\d+)($|\.)")


def compare(old, new):
    """old/new: {name: record}. Returns a dict describing the difference."""
    res = {'added': [], 'removed': [], 'statement_changed': [], 'body_changed': [], 'proof_changed': [],
           'kind_changed': [], 'aux_removed': [], 'aux_changed': []}
    for name, o in old.items():
        n = new.get(name)
        aux = bool(AUX.search(name))
        if n is None:
            res['aux_removed' if aux else 'removed'].append(name)
            continue
        if n['kind'] != o['kind']:
            res['kind_changed'].append(name)
        elif n['thash'] != o['thash'] or n['tsize'] != o['tsize']:
            res['aux_changed' if aux else 'statement_changed'].append(name)
        elif n['vhash'] != o['vhash'] or n['vsize'] != o['vsize']:
            if o['kind'] == 'thm':
                res['proof_changed'].append(name)
            else:
                res['aux_changed' if aux else 'body_changed'].append(name)
    for name in new:
        if name not in old:
            res['added'].append(name)
    breaking = res['removed'] + res['statement_changed'] + res['body_changed'] + res['kind_changed']
    res['compatible'] = not breaking
    res['breaking'] = sorted(breaking)
    res['aux_to_check'] = sorted(res['aux_removed'] + res['aux_changed'])
    return res


def check_module(module, new_root, old_root=None, old_path=None):
    """Compare a recompiled module with its accepted version (overlay if changed before, else base)."""
    old_p = old_path or (C.module_path(module, old_root, '.olean') if old_root else C.current_olean(module))
    new_p = C.module_path(module, new_root, '.olean')
    pairs = []
    if os.path.exists(old_p):
        pairs.append((module + '@old', old_p))
    if os.path.exists(new_p):
        pairs.append((module + '@new', new_p))
    mods = C.parse_consts(C.moddump(pairs)) if pairs else {}
    old = mods.get(module + '@old', {'decls': {}})['decls']
    new = mods.get(module + '@new', {'decls': {}})['decls']
    res = compare(old, new)
    res['module'] = module
    res['had_old'] = os.path.exists(old_p)
    res['has_new'] = os.path.exists(new_p)
    return res, old, new


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('module')
    ap.add_argument('--new', required=True)
    ap.add_argument('--old', default=None, help='root of the old compiled modules (default: the accepted state)')
    a = ap.parse_args()
    res, _, _ = check_module(a.module, a.new, a.old)
    if not res['has_new']:
        print(f'no recompiled module for {a.module} under {a.new}', file=sys.stderr)
        sys.exit(1)
    print(json.dumps(res, indent=1))
    sys.exit(0 if res['compatible'] else 2)


if __name__ == '__main__':
    main()
