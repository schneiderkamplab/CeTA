#!/usr/bin/env bash
# Compile only freshly generated Isabelle code. No proof/search implementation here.
set -euo pipefail
if [[ $# != 2 ]]; then
  echo "usage: $0 GENERATED_DIRECTORY NEW_OUTPUT_DIRECTORY" >&2
  exit 2
fi
lp_generated=$(realpath "$1")
lp_output=$(realpath -m "$2")
lp_source=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
test -f "$lp_generated/LP_Triples_Generated.hs"
[[ ! -e "$lp_output" ]] || { echo "Output already exists" >&2; exit 2; }
mkdir -p "$lp_output/obj"
"${GHC:-ghc}" -O0 -i"$lp_generated" -outputdir "$lp_output/obj" \
  "$lp_source/scripts/LP_Triples_Main.hs" -o "$lp_output/ceta-lp-triples" \
  >"$lp_output/build.log" 2>&1
sha256sum "$lp_generated"/*.hs "$lp_source/scripts/LP_Triples_Main.hs" \
  "$lp_output/ceta-lp-triples" >"$lp_output/checksums.sha256"
git -C "$lp_source" rev-parse HEAD >"$lp_output/source-commit.txt"
git -C "$lp_source" status --porcelain >"$lp_output/source-status.txt"
echo "$lp_output/ceta-lp-triples"
