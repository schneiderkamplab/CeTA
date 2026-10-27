#!/usr/bin/env bash
set -euo pipefail
[[ $# == 1 ]] || { echo "Usage: $0 NEW_OUTPUT_DIRECTORY" >&2; exit 2; }
ho_output=$(realpath -m "$1")
[[ ! -e "$ho_output" ]] || { echo "Output exists: $ho_output" >&2; exit 2; }
mkdir -p "$ho_output"
cd "$(dirname "${BASH_SOURCE[0]}")/.."
export USER_HOME="${HO_ISABELLE_USER_HOME:?Set a private Isabelle cache}"
export ISABELLE_IDENTIFIER="${HO_ISABELLE_IDENTIFIER:?Set its identifier}"
ho_isabelle="${ISABELLE_TOOL:-/work/dfm/festschrift/ferrum/.tools/Isabelle2025-2/bin/isabelle}"
{ time bash scripts/check_higher_order_guarded.sh; } >"$ho_output/isabelle-build.log" 2>&1
ho_dirs=()
for ho_part in Checker Beta Values Computability Priority Accessible Descent \
  Polynomial Semantic_Calls Lambda_Access Component_Order Functional_Access \
  Modular Meta Lex Blocked Prefix Guarded; do
  ho_dirs+=(-d "thys/Higher_Order_$ho_part")
done
"$ho_isabelle" export -n "${ho_dirs[@]}" -O "$ho_output/export" \
  -x '*:code/**' Higher_Order_Guarded >"$ho_output/export.log" 2>&1
ho_generated="$ho_output/export/Higher_Order_Guarded.Higher_Order_Guarded_Code/code/export1"
{ time "${GHC:-ghc}" -DHO_GUARDED -DHO_PREFIX -DHO_BLOCKED -O2 -i"$ho_generated" \
  -outputdir "$ho_output/ghc" src/Higher_Order_Main.hs \
  -o "$ho_output/ceta-higher-order"; } >"$ho_output/ghc-build.log" 2>&1
sha256sum "$ho_output/ceta-higher-order" "$ho_generated/Higher_Order_Checker.hs" \
  >"$ho_output/checksums.sha256"
git rev-parse HEAD >"$ho_output/source-commit.txt"
git diff -- src/Higher_Order_Main.hs >"$ho_output/source.diff"
sha256sum thys/Higher_Order_Prefix/*.thy thys/Higher_Order_Prefix/ROOT \
  thys/Higher_Order_Guarded/*.thy thys/Higher_Order_Guarded/ROOT \
  src/Higher_Order_Main.hs scripts/*higher_order_prefix*.sh scripts/*higher_order_guarded*.sh >"$ho_output/source-checksums.sha256"
echo "$ho_output/ceta-higher-order"
