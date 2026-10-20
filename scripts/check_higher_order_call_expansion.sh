#!/usr/bin/env bash
# A proof-only leaf; reuse private checked heaps and record command timings.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
export USER_HOME="${HO_ISABELLE_USER_HOME:?Set a private Isabelle cache}"
export ISABELLE_IDENTIFIER="${HO_ISABELLE_IDENTIFIER:?Set its identifier}"
ho_dirs=()
for ho_part in Checker Beta Values Computability Priority Accessible Descent \
  Polynomial Semantic_Calls Lambda_Access Component_Order Functional_Access \
  Modular Meta Lex Blocked Prefix Guarded; do
  ho_dirs+=(-d "thys/Higher_Order_$ho_part")
done
"${ISABELLE_TOOL:-/work/dfm/festschrift/ferrum/.tools/Isabelle2025-2/bin/isabelle}" \
  build -v -j1 -o threads=4 -o parallel_proofs=0 \
  -o build_timing_threshold=0.05 "${ho_dirs[@]}" \
  -D thys/Higher_Order_Call_Expansion Higher_Order_Call_Expansion
