#!/usr/bin/env python3
"""The small equivalence check: does a recompiled module still expose what it exposed before?

  tools/iface.py Development.Some.Module --new build/x [--old compiled/lib/lean]

Other modules never look inside a proof; they only see each theorem's statement, and each
definition's statement and body. So if a recompiled module has

  * every declaration the old one had,
  * with the same statement, written the same way: same argument names, same explicit and
    implicit arguments, same universe parameters in the same order,
  * for anything that is not a theorem, the same body,
  * registers the same things with Lean (attributes, instances, simp lemmas, notation,
    namespaces),
  * and imports the same modules,

then every already-compiled module that uses it is still a valid proof and needs no rebuild.
New declarations are harmless. Changed or missing ones are listed, so that only the modules
that actually use them need to be looked at.

Why the second and fourth points are spelled out: Lean's own hash of a statement ignores the
names of its arguments and whether each is explicit or implicit, and an attribute does not show
in any statement. A theorem replaced by an `alias` of another takes the other's argument names;
dropping `@[simp]` changes what `simp` does elsewhere. Both would pass a check on statements only.

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

# Extensions whose entries cannot change how another module elaborates: source positions,
# documentation, linter messages, bookkeeping about which imports were used, and the per-declaration
# axiom cache. Everything else must have the same number of entries before and after.
EXT_IGNORED = {'Lean.declRangeExt', 'Lean.docStringExt', 'Lean.Linter.lintLogExt', 'Batteries.Tactic.Alias.aliasExt'}
EXT_IGNORED_SUFFIX = ('.Lean.extraModUses', '.Lean.exportedAxiomsExt', '.Lean.namespacesExt')
# `theorem _root_.X ...` registers the root itself as a namespace; nothing can open it.
ROOT_ENTRY = '[anonymous]'


def compare(old, new):
    """old/new: {name: record}. Returns a dict describing the difference between declarations."""
    res = {'added': [], 'removed': [], 'statement_changed': [], 'signature_changed': [], 'body_changed': [],
           'proof_changed': [], 'kind_changed': [], 'aux_removed': [], 'aux_changed': []}
    for name, o in old.items():
        n = new.get(name)
        aux = bool(AUX.search(name))
        if n is None:
            res['aux_removed' if aux else 'removed'].append(name)
            continue
        strict = 'st' in o and 'st' in n
        if n['kind'] != o['kind']:
            res['kind_changed'].append(name)
        elif n['thash'] != o['thash'] or n['tsize'] != o['tsize']:
            res['aux_changed' if aux else 'statement_changed'].append(name)
        elif strict and (n['st'] != o['st'] or n['lp'] != o['lp']):
            # same statement up to argument names, explicit/implicit arguments or universe order
            res['aux_changed' if aux else 'signature_changed'].append(name)
        elif n['vhash'] != o['vhash'] or n['vsize'] != o['vsize']:
            if o['kind'] == 'thm':
                res['proof_changed'].append(name)
            else:
                res['aux_changed' if aux else 'body_changed'].append(name)
        elif strict and o['kind'] != 'thm' and n['sv'] != o['sv']:
            res['aux_changed' if aux else 'body_changed'].append(name)
    for name in new:
        if name not in old:
            res['added'].append(name)
    breaking = (res['removed'] + res['statement_changed'] + res['signature_changed'] + res['body_changed']
                + res['kind_changed'])
    res['compatible'] = not breaking
    res['breaking'] = sorted(breaking)
    res['aux_to_check'] = sorted(res['aux_removed'] + res['aux_changed'])
    return res


def compare_modules(old_mod, new_mod):
    """old_mod/new_mod: module records from common.parse_consts. Adds what the module registers:

      ext_changed    {extension: [entries before, entries after]} for extensions that matter
      ns_added       namespaces the new version registers and the old one did not
      ns_removed     the other way round (the root entry is ignored)
      strict         whether both sides carried the strict information

    `compatible` is False if a declaration broke, an extension count changed or a namespace was
    removed. Added namespaces are left to the caller (tools/nscheck.py decides whether they matter)."""
    old_mod = old_mod or {'decls': {}, 'ext': None, 'namespaces': None}
    new_mod = new_mod or {'decls': {}, 'ext': None, 'namespaces': None}
    res = compare(old_mod['decls'], new_mod['decls'])
    res['strict'] = old_mod.get('ext') is not None and new_mod.get('ext') is not None
    res['ext_changed'], res['ns_added'], res['ns_removed'] = {}, [], []
    # A changed import list changes what every file that imports this one can see, whatever the
    # module itself exposes.
    oi, ni = old_mod.get('imports'), new_mod.get('imports')
    res['imports_added'] = sorted(set(ni or ()) - set(oi or ())) if old_mod['decls'] else []
    res['imports_removed'] = sorted(set(oi or ()) - set(ni or ())) if old_mod['decls'] else []
    if res['imports_added'] or res['imports_removed']:
        res['compatible'] = False
    if res['strict']:
        oe, ne = old_mod['ext'], new_mod['ext']
        for k in sorted(set(oe) | set(ne)):
            if k in EXT_IGNORED or k.endswith(EXT_IGNORED_SUFFIX):
                continue
            if oe.get(k, 0) != ne.get(k, 0):
                res['ext_changed'][k] = [oe.get(k, 0), ne.get(k, 0)]
        ons, nns = set(old_mod.get('namespaces') or ()), set(new_mod.get('namespaces') or ())
        res['ns_added'] = sorted(nns - ons - {ROOT_ENTRY})
        res['ns_removed'] = sorted(ons - nns - {ROOT_ENTRY})
        if old_mod['decls'] and (res['ext_changed'] or res['ns_removed']):
            res['compatible'] = False
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
    res = compare_modules(mods.get(module + '@old'), mods.get(module + '@new'))
    old = (mods.get(module + '@old') or {'decls': {}})['decls']
    new = (mods.get(module + '@new') or {'decls': {}})['decls']
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
