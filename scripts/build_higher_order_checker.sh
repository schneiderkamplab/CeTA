#!/usr/bin/env bash
# Isolated, reproducible experimental higher-order checker build.
set -euo pipefail
if [[ $# != 1 ]]; then
  echo "Usage: $0 NEW_OUTPUT_DIRECTORY" >&2
  exit 2
fi
ho_source_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
ho_output=$(realpath -m "$1")
if [[ -e "$ho_output" ]]; then
  echo "Refusing to overwrite existing output: $ho_output" >&2
  exit 2
fi
ho_isabelle=${ISABELLE_TOOL:-/work/dfm/festschrift/ferrum/.tools/Isabelle2025-2/bin/isabelle}
ho_ghc=${GHC:-ghc}
mkdir -p "$ho_output"
# An explicitly supplied private cache reuses checked dependency heaps. Do not
# point this at a shared build identifier while another build is running there.
export USER_HOME="${HO_ISABELLE_USER_HOME:-$ho_output/isabelle-user}"
export ISABELLE_IDENTIFIER="${HO_ISABELLE_IDENTIFIER:-higher_order_isolated}"
cd "$ho_source_root"
{ time "$ho_isabelle" build -v -j1 -o threads=4 -o parallel_proofs=0 \
  -o build_timing_threshold=0.05 -d thys/Higher_Order_Checker -d thys/Higher_Order_Beta \
  -d thys/Higher_Order_Values -d thys/Higher_Order_Computability -D thys/Higher_Order_Polynomial Higher_Order_Polynomial \
  ; } >"$ho_output/isabelle-build.log" 2>&1
"$ho_isabelle" export -n -d thys/Higher_Order_Checker -d thys/Higher_Order_Beta \
  -d thys/Higher_Order_Values -d thys/Higher_Order_Computability -d thys/Higher_Order_Polynomial -O "$ho_output/export" \
  -x '*:code/**' Higher_Order_Polynomial >"$ho_output/export.log" 2>&1
ho_generated="$ho_output/export/Higher_Order_Polynomial.Higher_Order_Polynomial_Code/code/export1"
{ time "$ho_ghc" -O1 -i"$ho_generated" -outputdir "$ho_output/ghc" \
  src/Higher_Order_Main.hs -o "$ho_output/ceta-higher-order"; } >"$ho_output/ghc-build.log" 2>&1
sha256sum "$ho_output/ceta-higher-order" "$ho_generated/Higher_Order_Checker.hs" \
  >"$ho_output/checksums.sha256"
git rev-parse HEAD >"$ho_output/source-commit.txt"
git diff -- thys/Higher_Order_Checker thys/Higher_Order_Beta thys/Higher_Order_Values \
  thys/Higher_Order_Computability thys/Higher_Order_Polynomial src/Higher_Order_Main.hs scripts/build_higher_order_checker.sh \
  >"$ho_output/source.diff"
sha256sum thys/Higher_Order_Checker/*.thy thys/Higher_Order_Checker/ROOT \
  thys/Higher_Order_Beta/*.thy thys/Higher_Order_Beta/ROOT thys/Higher_Order_Beta/Isabelle_Lambda/*.thy \
  thys/Higher_Order_Values/*.thy thys/Higher_Order_Values/ROOT \
  thys/Higher_Order_Computability/*.thy thys/Higher_Order_Computability/ROOT \
  thys/Higher_Order_Polynomial/*.thy thys/Higher_Order_Polynomial/ROOT \
  src/Higher_Order_Main.hs scripts/build_higher_order_checker.sh >"$ho_output/source-checksums.sha256"
echo "$ho_output/ceta-higher-order"
