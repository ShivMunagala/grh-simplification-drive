#!/usr/bin/env bash
# Download Alpöge's Lean archive, verify it, and extract it into proof/.
#
#   tools/fetch_upstream.sh            # download (if needed), verify, extract
#   PARTS_DIR=/some/dir tools/fetch_upstream.sh   # reuse parts already downloaded there
#
# The archive is 14 parts that join into one tar.gz. Nothing in it is executed here.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PARTS_DIR="${PARTS_DIR:-$ROOT/upstream-dl}"
DEST="$ROOT/proof"
BASE_URL="https://alpo.ge/lean.tar.gz.part"
SHA256="9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc"
EXPECTED_FILES=175190   # 175,187 .lean + lakefile.toml + lake-manifest.json + lean-toolchain

mkdir -p "$PARTS_DIR"
for i in 01 02 03 04 05 06 07 08 09 10 11 12 13 14; do
  f="$PARTS_DIR/lean.tar.gz.part$i"
  if [ ! -s "$f" ]; then
    echo "downloading part $i"
    curl -sS -L --retry 3 -o "$f" "$BASE_URL$i"
  fi
done

got="$(cat "$PARTS_DIR"/lean.tar.gz.part* | sha256sum | cut -d' ' -f1)"
if [ "$got" != "$SHA256" ]; then
  echo "sha256 mismatch: got $got, expected $SHA256" >&2
  exit 1
fi
echo "sha256 ok: $got"

# Refuse archives containing anything but plain files under lean/.
bad="$(cat "$PARTS_DIR"/lean.tar.gz.part* | tar tzvf - | awk '$1 !~ /^-/ || $6 !~ /^lean\// || $6 ~ /\.\./' | head -5)"
if [ -n "$bad" ]; then
  echo "unexpected archive members:" >&2
  echo "$bad" >&2
  exit 1
fi

if [ -e "$DEST" ] && [ -n "$(ls -A "$DEST" 2>/dev/null)" ]; then
  echo "$DEST is not empty; refusing to overwrite" >&2
  exit 1
fi
mkdir -p "$DEST"
cat "$PARTS_DIR"/lean.tar.gz.part* \
  | tar xzf - --no-same-owner --no-same-permissions --strip-components=1 -C "$DEST"

n="$(find "$DEST" -type f | wc -l)"
if [ "$n" != "$EXPECTED_FILES" ]; then
  echo "file count mismatch: got $n, expected $EXPECTED_FILES" >&2
  exit 1
fi
echo "extracted $n files into $DEST"
