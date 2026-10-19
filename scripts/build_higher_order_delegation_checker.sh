#!/usr/bin/env bash
# Source-bound higher-order delegation + ordinary CeTA CPF checker.
set -euo pipefail
if [[ $# != 1 ]]; then
  echo 'Usage: build_higher_order_delegation_checker.sh NEW_OUTPUT_DIRECTORY' >&2
  exit 2
fi
ho_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
ho_output=$(realpath -m "$1")
if [[ -e "$ho_output" ]]; then
  echo "Refusing to overwrite $ho_output" >&2
  exit 2
fi
: "${HO_ISABELLE_USER_HOME:?Supply an isolated user directory with checked dependency heaps}"
: "${HO_ISABELLE_IDENTIFIER:?Supply its isolated Isabelle identifier}"
: "${HO_CETA_SOURCE_DIR:?Supply the source tree matching the cached production checker}"
: "${AFP:?Supply the matching AFP source directory}"
ho_isabelle=${ISABELLE_TOOL:-/work/dfm/festschrift/ferrum/.tools/Isabelle2025-2/bin/isabelle}
ho_ghc=${GHC:-ghc}
export USER_HOME="$HO_ISABELLE_USER_HOME" ISABELLE_IDENTIFIER="$HO_ISABELLE_IDENTIFIER"
mkdir -p "$ho_output"
cd "$ho_root"
ho_dirs=()
for ho_dir in thys/Higher_Order_*; do
  if [[ -f "$ho_dir/ROOT" ]]; then ho_dirs+=(-d "$ho_dir"); fi
done
{ time "$ho_isabelle" build -v -b -j1 -o threads=4 -o parallel_proofs=0 \
    -o build_timing_threshold=0.05 -d "$HO_CETA_SOURCE_DIR/thys" \
    "${ho_dirs[@]}" Higher_Order_CeTA_Code; } >"$ho_output/isabelle-build.log" 2>&1
"$ho_isabelle" export -n -d "$HO_CETA_SOURCE_DIR/thys" "${ho_dirs[@]}" \
  -O "$ho_output/export" -x '*:code/**' Higher_Order_CeTA_Code >"$ho_output/export.log" 2>&1
ho_generated="$ho_output/export/Higher_Order_CeTA_Code.Higher_Order_CeTA_Code/code/export1"
{ time "$ho_ghc" -O1 -i"$ho_generated" -outputdir "$ho_output/ghc" \
    src/Higher_Order_Delegation_Main.hs -o "$ho_output/ceta-ho-delegation"; } \
    >"$ho_output/ghc-build.log" 2>&1
git rev-parse HEAD >"$ho_output/source-commit.txt"
git diff -- thys/Higher_Order_* src/Higher_Order_Delegation_Main.hs \
  scripts/build_higher_order_delegation_checker.sh >"$ho_output/source.diff"
sha256sum thys/Higher_Order_*/*.thy thys/Higher_Order_*/ROOT \
  thys/Higher_Order_Beta/Isabelle_Lambda/*.thy src/Higher_Order_Delegation_Main.hs \
  scripts/build_higher_order_delegation_checker.sh >"$ho_output/source-checksums.sha256"
sha256sum "$ho_output/ceta-ho-delegation" "$ho_generated"/*.hs >"$ho_output/checksums.sha256"
echo "$ho_output/ceta-ho-delegation"
