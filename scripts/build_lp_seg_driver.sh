#!/usr/bin/env bash
# Link verified exports, reusing existing checked heaps/generated modules.
# Generate modules with Logic_Programming_SEG_Code; never edit generated code.
set -euo pipefail
if [[ $# != 3 && $# != 4 ]]; then
  echo "usage: $0 RETURN_EXPORT_DIRECTORY SEG_EXPORT_DIRECTORY NEW_OUTPUT_DIRECTORY [PRIOR_GHC_OBJECT_DIRECTORY]" >&2
  exit 2
fi
lp_return=$(realpath "$1")
lp_seg=$(realpath "$2")
lp_output=$(realpath -m "$3")
lp_source=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
[[ ! -e "$lp_output" ]] || { echo "Output already exists" >&2; exit 2; }
test -f "$lp_return/LP_Return_Module_Generated.hs"
test -f "$lp_seg/LP_SEG_Certificate_Generated.hs"
# Search-path order must not select different versions of shared support code.
for lp_file in "$lp_return"/*.hs; do
  lp_name=$(basename "$lp_file")
  if [[ -f "$lp_seg/$lp_name" ]]; then cmp "$lp_file" "$lp_seg/$lp_name"; fi
done
mkdir -p "$lp_output/obj"
if [[ $# == 4 ]]; then
  lp_prior=$(realpath "$4")
  test -d "$lp_prior"
  # GHC performs its normal source/interface/flag dependency checks. Never
  # manually link a retained object or bypass the recompilation checker.
  cp -a "$lp_prior/." "$lp_output/obj/"
  echo "$lp_prior" >"$lp_output/reused-object-cache.txt"
fi
lp_opt=${LP_SEG_GHC_OPT:--O1}
lp_main="$lp_source/scripts/LP_Cut_SEG_Main.hs"
lp_extra=()
if [[ -n "${LP_NO_EXPORT_DIRECTORY:-}" ]]; then
  lp_no=$(realpath "$LP_NO_EXPORT_DIRECTORY")
  test -f "$lp_no/LP_Cut_NO_Generated.hs"
  for lp_file in "$lp_no"/*.hs; do
    lp_name=$(basename "$lp_file")
    for lp_existing in "$lp_return" "$lp_seg"; do
      if [[ -f "$lp_existing/$lp_name" ]]; then cmp "$lp_file" "$lp_existing/$lp_name"; fi
    done
  done
  lp_extra=(-i"$lp_no")
  lp_main="$lp_source/scripts/LP_Cut_NO_Main.hs"
fi
if [[ -n "${LP_PROJECTED_EXPORT_DIRECTORY:-}" ]]; then
  test -n "${LP_NO_EXPORT_DIRECTORY:-}"
  lp_projected=$(realpath "$LP_PROJECTED_EXPORT_DIRECTORY")
  test -f "$lp_projected/LP_Cut_Projected_Generated.hs"
  for lp_file in "$lp_projected"/*.hs; do
    lp_name=$(basename "$lp_file")
    for lp_existing in "$lp_return" "$lp_seg" "$lp_no"; do
      if [[ -f "$lp_existing/$lp_name" ]]; then cmp "$lp_file" "$lp_existing/$lp_name"; fi
    done
  done
  lp_extra+=(-i"$lp_projected")
  lp_main="$lp_source/scripts/LP_Cut_Integrated_Main.hs"
fi
if [[ -n "${LP_SEG_PROJECTED_EXPORT_DIRECTORY:-}" ]]; then
  test -n "${LP_PROJECTED_EXPORT_DIRECTORY:-}"
  lp_seg_projected=$(realpath "$LP_SEG_PROJECTED_EXPORT_DIRECTORY")
  test -f "$lp_seg_projected/LP_SEG_Projected_Generated.hs"
  for lp_file in "$lp_seg_projected"/*.hs; do
    lp_name=$(basename "$lp_file")
    for lp_existing in "$lp_return" "$lp_seg" "$lp_no" "$lp_projected"; do
      if [[ -f "$lp_existing/$lp_name" ]]; then cmp "$lp_file" "$lp_existing/$lp_name"; fi
    done
  done
  lp_extra+=(-i"$lp_seg_projected" -DLP_SEG_PROJECTED)
fi
if [[ -n "${LP_SEG_TRIPLES_EXPORT_DIRECTORY:-}" ]]; then
  test -n "${LP_PROJECTED_EXPORT_DIRECTORY:-}"
  lp_triples=$(realpath "$LP_SEG_TRIPLES_EXPORT_DIRECTORY")
  test -f "$lp_triples/LP_Triples_Generated.hs"
  for lp_file in "$lp_triples"/*.hs; do
    lp_name=$(basename "$lp_file")
    for lp_existing in "$lp_return" "$lp_seg" "$lp_no" "$lp_projected" "${lp_seg_projected:-$lp_seg}"; do
      if [[ -f "$lp_existing/$lp_name" ]]; then cmp "$lp_file" "$lp_existing/$lp_name"; fi
    done
  done
  lp_extra+=(-i"$lp_triples" -DLP_SEG_TRIPLES)
fi
case "$lp_opt" in -O0|-O1|-O2) ;; *) echo "Invalid GHC optimization level" >&2; exit 2;; esac
echo "$lp_opt" >"$lp_output/ghc-optimization.txt"
"${GHC:-ghc}" "$lp_opt" -i"$lp_return" -i"$lp_seg" "${lp_extra[@]}" -outputdir "$lp_output/obj" \
  "$lp_main" -o "$lp_output/ceta-lp-seg" \
  >"$lp_output/build.log" 2>&1
sha256sum "$lp_return"/*.hs "$lp_seg"/*.hs "$lp_main" \
  "$lp_output/ceta-lp-seg" >"$lp_output/checksums.sha256"
if [[ -n "${LP_NO_EXPORT_DIRECTORY:-}" ]]; then
  sha256sum "$lp_no"/*.hs >>"$lp_output/checksums.sha256"
fi
git -C "$lp_source" rev-parse HEAD >"$lp_output/source-commit.txt"
if [[ -n "${LP_PROJECTED_EXPORT_DIRECTORY:-}" ]]; then
  sha256sum "$lp_projected"/*.hs >>"$lp_output/checksums.sha256"
fi
if [[ -n "${LP_SEG_PROJECTED_EXPORT_DIRECTORY:-}" ]]; then
  sha256sum "$lp_seg_projected"/*.hs >>"$lp_output/checksums.sha256"
fi
if [[ -n "${LP_SEG_TRIPLES_EXPORT_DIRECTORY:-}" ]]; then
  sha256sum "$lp_triples"/*.hs >>"$lp_output/checksums.sha256"
fi
echo "$lp_output/ceta-lp-seg"
