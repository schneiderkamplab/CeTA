#!/usr/bin/env bash
# Isolated blocked-call extension; legacy and protected checkers remain unchanged.
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
  -d thys/Higher_Order_Values -d thys/Higher_Order_Computability -d thys/Higher_Order_Priority -d thys/Higher_Order_Accessible -d thys/Higher_Order_Descent -d thys/Higher_Order_Polynomial -d thys/Higher_Order_Semantic_Calls -d thys/Higher_Order_Lambda_Access -d thys/Higher_Order_Component_Order -d thys/Higher_Order_Functional_Access -d thys/Higher_Order_Modular -d thys/Higher_Order_Meta -d thys/Higher_Order_Lex -D thys/Higher_Order_Blocked Higher_Order_Blocked \
  ; } >"$ho_output/isabelle-build.log" 2>&1
"$ho_isabelle" export -n -d thys/Higher_Order_Checker -d thys/Higher_Order_Beta \
  -d thys/Higher_Order_Values -d thys/Higher_Order_Computability -d thys/Higher_Order_Priority -d thys/Higher_Order_Accessible -d thys/Higher_Order_Descent -d thys/Higher_Order_Polynomial -d thys/Higher_Order_Semantic_Calls -d thys/Higher_Order_Lambda_Access -d thys/Higher_Order_Component_Order -d thys/Higher_Order_Functional_Access -d thys/Higher_Order_Modular -d thys/Higher_Order_Meta -d thys/Higher_Order_Lex -d thys/Higher_Order_Blocked -O "$ho_output/export" \
  -x '*:code/**' Higher_Order_Blocked >"$ho_output/export.log" 2>&1
ho_generated="$ho_output/export/Higher_Order_Blocked.Higher_Order_Blocked_Code/code/export1"
{ time "$ho_ghc" -DHO_BLOCKED -O2 -i"$ho_generated" -outputdir "$ho_output/ghc" \
  src/Higher_Order_Main.hs -o "$ho_output/ceta-higher-order"; } >"$ho_output/ghc-build.log" 2>&1
sha256sum "$ho_output/ceta-higher-order" "$ho_generated/Higher_Order_Checker.hs" \
  >"$ho_output/checksums.sha256"
git rev-parse HEAD >"$ho_output/source-commit.txt"
git diff -- thys/Higher_Order_Checker thys/Higher_Order_Beta thys/Higher_Order_Values \
  thys/Higher_Order_Computability thys/Higher_Order_Priority thys/Higher_Order_Accessible thys/Higher_Order_Descent thys/Higher_Order_Polynomial thys/Higher_Order_Semantic_Calls thys/Higher_Order_Lambda_Access thys/Higher_Order_Component_Order thys/Higher_Order_Functional_Access thys/Higher_Order_Modular thys/Higher_Order_Meta thys/Higher_Order_Lex thys/Higher_Order_Blocked src/Higher_Order_Main.hs scripts/build_higher_order_blocked_checker.sh \
  >"$ho_output/source.diff"
sha256sum thys/Higher_Order_Checker/*.thy thys/Higher_Order_Checker/ROOT \
  thys/Higher_Order_Beta/*.thy thys/Higher_Order_Beta/ROOT thys/Higher_Order_Beta/Isabelle_Lambda/*.thy \
  thys/Higher_Order_Values/*.thy thys/Higher_Order_Values/ROOT \
  thys/Higher_Order_Computability/*.thy thys/Higher_Order_Computability/ROOT \
  thys/Higher_Order_Priority/*.thy thys/Higher_Order_Priority/ROOT \
  thys/Higher_Order_Accessible/*.thy thys/Higher_Order_Accessible/ROOT \
  thys/Higher_Order_Descent/*.thy thys/Higher_Order_Descent/ROOT \
  thys/Higher_Order_Polynomial/*.thy thys/Higher_Order_Polynomial/ROOT \
  thys/Higher_Order_Semantic_Calls/*.thy thys/Higher_Order_Semantic_Calls/ROOT \
  thys/Higher_Order_Lambda_Access/*.thy thys/Higher_Order_Lambda_Access/ROOT \
  thys/Higher_Order_Component_Order/*.thy thys/Higher_Order_Component_Order/ROOT \
  thys/Higher_Order_Functional_Access/*.thy thys/Higher_Order_Functional_Access/ROOT \
  thys/Higher_Order_Modular/*.thy thys/Higher_Order_Modular/ROOT \
  thys/Higher_Order_Meta/*.thy thys/Higher_Order_Meta/ROOT \
  thys/Higher_Order_Lex/*.thy thys/Higher_Order_Lex/ROOT \
  thys/Higher_Order_Blocked/*.thy thys/Higher_Order_Blocked/ROOT \
  src/Higher_Order_Main.hs scripts/build_higher_order_blocked_checker.sh >"$ho_output/source-checksums.sha256"
echo "$ho_output/ceta-higher-order"
