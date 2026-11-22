#!/usr/bin/env bash
# Set up a rented machine for batch work: Lean, the proof with our patches, Mathlib's compiled
# cache, the compiled base (unpacked), and the module reader.
#
# Run from the repository root on the machine, after copying this repository's tools/, patches/
# and baseline/ there. Needs about 260 GB of disk and ideally 128 GB or more of memory.
# Safe to re-run: each step is skipped if its result is already there.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"
export DEBIAN_FRONTEND=noninteractive

step() { echo; echo "=== $* ($(date -u +%H:%M:%S))"; }

step "packages"
if ! command -v zstd >/dev/null || ! command -v git >/dev/null || ! command -v rsync >/dev/null; then
  apt-get update -qq
  apt-get install -y -qq git curl zstd python3 rsync ca-certificates build-essential >/dev/null
fi

step "lean"
if [ ! -x "$HOME/.elan/bin/lake" ]; then
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain leanprover/lean4:v4.33.1 >/dev/null
fi
export PATH="$HOME/.elan/bin:$PATH"
lean --version

step "proof (archive + patches)"
tools/setup_proof.sh

step "mathlib compiled cache"
if [ ! -f proof/.lake/.mathlib_cache_ok ]; then
  ulimit -n 65536 || true        # the cache unpacker opens thousands of files at once
  (cd proof && lake exe cache get)
  test -f proof/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean
  touch proof/.lake/.mathlib_cache_ok
fi

step "compiled base: download"
if [ ! -f compiled/.unpacked ]; then
  tools/fetch_compiled.sh
  step "compiled base: unpack"
  mkdir -p compiled/lib/lean
  zstd -dc --long=31 upstream-dl/compiled/oleans.tar.zst \
    | tar x --strip-components=4 -C compiled/lib/lean --wildcards '*.olean'
  touch compiled/.unpacked
  rm -f upstream-dl/compiled/oleans.tar.zst
fi

step "module reader"
lake -d tools/moddump build

step "ready"
df -h "$ROOT" | tail -1
free -g | sed -n 2p
nproc
