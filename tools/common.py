"""Shared paths and helpers for the grh tools."""
import json, os, resource, subprocess, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROOF = os.path.join(ROOT, 'proof')          # working copy of the proof: its own local git repository
SRC = os.path.join(PROOF, 'src')
PATCHES = os.path.join(ROOT, 'patches')      # our changes to the proof, as stored in this repository
UPSTREAM_TAG = 'upstream'                    # tag of the unmodified archive inside proof/
COMPILED = os.path.join(ROOT, 'compiled', 'lib', 'lean')        # compiled modules of the base version
DATA_BASE = os.path.join(ROOT, 'data', 'base')
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


def package_libs():
    return [os.path.join(PACKAGES, p, '.lake', 'build', 'lib', 'lean') for p in PACKAGE_NAMES]


def module_path(module, root=SRC, ext='.lean'):
    return os.path.join(root, module.replace('.', os.sep) + ext)


def sandbox(cmd, ro=(), rw=(), env=None):
    """Wrap a command in bubblewrap: no network, read-only filesystem, home hidden except `ro`/`rw` paths."""
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
    if mem_gb:
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


def moddump(pairs, extra=('--noshared',)):
    """Run moddump (sandboxed) on (module, olean path) pairs; return its output lines as bytes."""
    tooldir = os.path.dirname(MODDUMP)
    dirs = sorted({os.path.dirname(os.path.abspath(p)) for _, p in pairs})
    cmd = sandbox([MODDUMP] + list(extra), ro=[tooldir] + dirs)
    inp = ''.join(f'{m}\t{os.path.abspath(p)}\n' for m, p in pairs).encode()
    p = subprocess.run(cmd, input=inp, stdout=subprocess.PIPE)
    if p.returncode != 0:
        raise RuntimeError(f'moddump failed rc={p.returncode}')
    return p.stdout.split(b'\n')


def parse_consts(lines):
    """Parse moddump output into {module: {name: record}}."""
    mods = {}
    cur = None
    for line in lines:
        if not line:
            continue
        f = line.split(b'\t', 9)
        tag = f[0]
        if tag == b'M':
            cur = f[1].decode()
            mods[cur] = {'imports': f[3].decode().split(',') if len(f) > 3 and f[3] else [], 'decls': {}, 'error': None}
        elif tag == b'C' and len(f) == 10 and cur is not None:
            mods[cur]['decls'][f[9].decode('utf-8', 'replace')] = {
                'kind': f[1].decode(), 'id': int(f[2]), 'tsize': int(f[3]), 'vsize': int(f[4]),
                'thash': int(f[5]), 'vhash': int(f[6]),
                'tdeps': [int(x) for x in f[7].split(b' ')] if f[7] else [],
                'vdeps': [int(x) for x in f[8].split(b' ')] if f[8] else [],
            }
        elif tag == b'X':
            m = f[1].decode()
            mods.setdefault(m, {'imports': [], 'decls': {}, 'error': None})['error'] = b'\t'.join(f[2:]).decode('utf-8', 'replace')
    return mods


def load_json(path, default=None):
    try:
        with open(path) as fh:
            return json.load(fh)
    except OSError:
        return default
