#!/usr/bin/env bash
# Build proof/: fetch the archive, make it a local git repository, apply our patches.
#
# proof/ is not stored in this repository. It is Alpöge's archive (fetched and checked by
# sha256) with patches/ applied on top. The first commit of proof/ is the unmodified archive,
# tagged `upstream`; everything after it is ours.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PROOF="$ROOT/proof"

if [ -d "$PROOF/.git" ]; then
  echo "proof/ is already set up"
  python3 "$ROOT/tools/patches.py" status
  exit 0
fi

"$ROOT/tools/fetch_upstream.sh"

git init -q -b main "$PROOF"
printf '.lake/\n*.olean\n*.ilean\n' > "$PROOF/.git/info/exclude"
git -C "$PROOF" add -A
if ! git -C "$PROOF" config user.name >/dev/null; then
  git -C "$PROOF" config user.name "grh setup"
  git -C "$PROOF" config user.email "grh@localhost"
fi
git -C "$PROOF" commit -q -m "Upstream archive, unmodified"
git -C "$PROOF" tag upstream

python3 "$ROOT/tools/patches.py" apply
python3 "$ROOT/tools/patches.py" status
