#!/usr/bin/env bash
# Download the published compiled build of the unmodified archive and verify it.
#
# 28.6 GB compressed, 99 GB unpacked (175,187 .olean/.ilean pairs), built by Jack McCarthy with
# Lean v4.33.1 in a sandbox; see the dataset README for how. The files come from compiling
# untrusted code: use them as data, inside a sandbox, never as something to trust.
#
# After this, run:
#   lake -d tools/moddump build
#   python3 tools/dump_stream.py --archive upstream-dl/compiled/oleans.tar.zst \
#       --out data/base --keep compiled/lib/lean
#   python3 tools/cone.py --out data/base
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
DEST="$ROOT/upstream-dl/compiled"
REV="9036e64326acf4acfae159b96664e9708445c1d1"
URL="https://huggingface.co/datasets/JackMcCarthy/riemann-hypothesis-build/resolve/$REV/oleans.tar.zst"
SHA256="953bab5386a7849527a11960f80a2fab427c49c637d6e94cc75788dd8f40196b"

mkdir -p "$DEST"
curl -sS -L --retry 5 -C - -o "$DEST/oleans.tar.zst" "$URL"
got="$(sha256sum "$DEST/oleans.tar.zst" | cut -d' ' -f1)"
if [ "$got" != "$SHA256" ]; then
  echo "sha256 mismatch: got $got, expected $SHA256" >&2
  exit 1
fi
echo "sha256 ok: $got"
