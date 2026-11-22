"""Shared paths and helpers for the grh tools."""
import json, os, resource, shutil, subprocess, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROOF = os.path.join(ROOT, 'proof')          # working copy of the proof: its own local git repository
SRC = os.path.join(PROOF, 'src')
PATCHES = os.path.join(ROOT, 'patches')      # our changes to the proof, as stored in this repository
UPSTREAM_TAG = 'upstream'                    # tag of the unmodified archive inside proof/
COMPILED = os.path.join(ROOT, 'compiled', 'lib', 'lean')        # compiled modules of the base version
DATA_BASE = os.path.join(ROOT, 'data', 'base')
# Accepted changes stack on top of the base: the compiled form of every module they touched,
# and the table rows for those modules. Together with the base this is "the accepted state".
OVERLAY = os.path.join(ROOT, 'compiled-overlay', 'lib', 'lean')
DATA_OVERLAY = os.path.join(ROOT, 'data', 'overlay')
STATE = os.path.join(DATA_OVERLAY, 'state.json')
LOCK = os.path.join(ROOT, 'build', '.compile.lock')             # one compiler at a time on this machine
MODDUMP = os.path.join(ROOT, 'tools', 'moddump', '.lake', 'build', 'bin', 'moddump')

TOOLCHAIN = os.path.expanduser('~/.elan/toolchains/leanprover--lean4---v4.33.1')
LEAN = os.path.join(TOOLCHAIN, 'bin', 'lean')

def _local_config():
    try:
        with open(os.path.join(ROOT, 'grh.local.json')) as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return {}


# Mathlib and its dependencies, compiled: Mathlib 0df444a built with Lean v4.33.1.
# By default the copy that `lake exe cache get` puts under proof/.lake/packages. To reuse a copy
# that already exists elsewhere, set GRH_PACKAGES or put {"packages": "/path"} in grh.local.json.
PACKAGES = (os.environ.get('GRH_PACKAGES') or _local_config().get('packages')
            or os.path.join(PROOF, '.lake', 'packages'))
PACKAGE_NAMES = ['mathlib', 'batteries', 'aesop', 'Qq', 'proofwidgets', 'plausible', 'importGraph',
                 'LeanSearchClient', 'Cli']

# Options from the archive's lakefile.toml.
LEAN_OPTS = ['-DautoImplicit=false', '-DrelaxedAutoImplicit=false', '-DmaxSynthPendingDepth=3',
             '-Dpp.unicode.fun=true', '-DmaxHeartbeats=4000000', '--tstack=400000']
FIELDS_PREFIXES = ('GroundTheory.LocalFields.', 'GroundTheory.GlobalFields.')
FIELDS_OPTS = ['-DsynthInstance.maxHeartbeats=400000']

TARGETS = ['riemannHypothesis', 'riemannZeta_eq_zero_re', 'LFunction_ne_zero_of_half_lt_re',
           'LFunction_eq_zero_re', 'LFunction_eq_zero_re_of_isPrimitive']

# ids (name hashes) of declarations whose use is never acceptable in a submission
FORBIDDEN = {
    5207765522374246084: 'sorryAx',
    15389850631415614753: 'Lean.ofReduceBool',
    4149518281782852217: 'Lean.trustCompiler',
}


def accepted_state():
    """State left by the last recorded change: proof commit, dials, modules in the overlay."""
    try:
        with open(STATE) as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return None


def current_olean(module):
    """Compiled form of a module in the accepted state: overlay if it was changed, else the base."""
    p = module_path(module, OVERLAY, '.olean')
    return p if os.path.exists(p) else module_path(module, COMPILED, '.olean')


def package_libs():
    return [os.path.join(PACKAGES, p, '.lake', 'build', 'lib', 'lean') for p in PACKAGE_NAMES]


def module_path(module, root=SRC, ext='.lean'):
    return os.path.join(root, module.replace('.', os.sep) + ext)


NO_SANDBOX = os.environ.get('GRH_NO_SANDBOX') == '1'     # set inside a disposable rented container


def sandbox(cmd, ro=(), rw=(), env=None):
    """Wrap a command in bubblewrap: no network, read-only filesystem, home hidden except `ro`/`rw` paths.

    With GRH_NO_SANDBOX=1 the command runs directly with a clean environment. That is for a rented,
    throw-away container, which is itself the sandbox and usually cannot nest another one."""
    if NO_SANDBOX:
        base = {'PATH': '/usr/local/bin:/usr/bin:/bin', 'HOME': '/tmp', 'LANG': 'C.UTF-8'}
        base.update(env or {})
        return ['env', '-i'] + [f'{k}={v}' for k, v in base.items()] + list(cmd)
    out = ['bwrap', '--unshare-all', '--die-with-parent',
           '--ro-bind', '/', '/', '--dev', '/dev', '--proc', '/proc',
           '--tmpfs', '/tmp', '--tmpfs', '/home']
    for p in ro:
        out += ['--ro-bind', p, p]
    for p in rw:
        out += ['--bind', p, p]
    out += ['--clearenv', '--setenv', 'PATH', '/usr/bin:/bin', '--setenv', 'HOME', '/tmp',
            '--setenv', 'LANG', 'C.UTF-8']
    for k, v in (env or {}).items():
        out += ['--setenv', k, v]
    return out + ['--'] + list(cmd)


def run_timed(cmd, mem_gb=None, stdin=None, stdout=None, stderr=None, timeout=None):
    """Run a command; return (rc, cpu seconds, wall seconds, max RSS in MB)."""
    if mem_gb and not NO_SANDBOX and shutil.which('systemd-run'):
        cmd = ['systemd-run', '--user', '--scope', '-q', '-p', f'MemoryMax={int(mem_gb * 1024)}M',
               '-p', 'MemorySwapMax=0'] + list(cmd)
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    t0 = time.time()
    try:
        p = subprocess.run(cmd, stdin=stdin, stdout=stdout, stderr=stderr, timeout=timeout)
        rc = p.returncode
    except subprocess.TimeoutExpired:
        rc = -999
    wall = time.time() - t0
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = (after.ru_utime - before.ru_utime) + (after.ru_stime - before.ru_stime)
    return rc, cpu, wall, after.ru_maxrss / 1024.0


def moddump(pairs, extra=('--noshared', '--strict')):
    """Run moddump (sandboxed) on (module, olean path) pairs; return its output lines as bytes.

    `--strict` adds, per declaration, hashes that also cover argument names and kinds, and per
    module what it registers with Lean (see tools/moddump/ModDump.lean)."""
    tooldir = os.path.dirname(MODDUMP)
    # everything normally lives under the repository; bind that once, plus any stray directories
    dirs = sorted({os.path.dirname(os.path.abspath(p)) for _, p in pairs
                   if not os.path.abspath(p).startswith(ROOT + os.sep)})
    cmd = sandbox([MODDUMP] + list(extra), ro=[tooldir, ROOT] + dirs)
    inp = ''.join(f'{m}\t{os.path.abspath(p)}\n' for m, p in pairs).encode()
    p = subprocess.run(cmd, input=inp, stdout=subprocess.PIPE)
    if p.returncode != 0:
        raise RuntimeError(f'moddump failed rc={p.returncode}')
    return p.stdout.split(b'\n')


def parse_consts(lines):
    """Parse moddump output into {module: {'decls': {name: record}, 'imports', 'ext', 'namespaces', 'error'}}.

    `ext` (extension -> number of entries) and `namespaces` are None unless moddump ran with
    --strict; a declaration record then also has 'st', 'sv', 'lp' (strict statement hash, strict
    body hash, universe parameter hash)."""
    mods = {}
    cur = None
    last = None
    for line in lines:
        if not line:
            continue
        f = line.split(b'\t', 9)
        tag = f[0]
        if tag == b'M':
            cur = f[1].decode()
            last = None
            mods[cur] = {'imports': f[3].decode().split(',') if len(f) > 3 and f[3] else [], 'decls': {}, 'error': None,
                         'ext': None, 'namespaces': None}
        elif tag == b'C' and len(f) == 10 and cur is not None:
            last = mods[cur]['decls'][f[9].decode('utf-8', 'replace')] = {
                'kind': f[1].decode(), 'id': int(f[2]), 'tsize': int(f[3]), 'vsize': int(f[4]),
                'thash': int(f[5]), 'vhash': int(f[6]),
                'tdeps': [int(x) for x in f[7].split(b' ')] if f[7] else [],
                'vdeps': [int(x) for x in f[8].split(b' ')] if f[8] else [],
            }
        elif tag == b'S' and last is not None and len(f) >= 5 and int(f[1]) == last['id']:
            last['st'], last['sv'], last['lp'] = int(f[2]), int(f[3]), int(f[4])
        elif tag == b'A' and cur is not None:
            ext = {}
            for kv in (f[2].decode().split(',') if len(f) > 2 and f[2] else []):
                k, _, v = kv.rpartition('=')
                ext[k] = int(v)
            mods[cur]['ext'] = ext
        elif tag == b'N' and cur is not None:
            mods[cur]['namespaces'] = f[2].decode().split(',') if len(f) > 2 and f[2] else []
        elif tag == b'X':
            m = f[1].decode()
            mods.setdefault(m, {'imports': [], 'decls': {}, 'error': None, 'ext': None, 'namespaces': None})['error'] = \
                b'\t'.join(f[2:]).decode('utf-8', 'replace')
    return mods


def load_json(path, default=None):
    try:
        with open(path) as fh:
            return json.load(fh)
    except OSError:
        return default
