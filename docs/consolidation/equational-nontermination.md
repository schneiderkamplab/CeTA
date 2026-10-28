---
type: Historical Report
---
# Equational nontermination integration — 2026-10-19

`thys/Proof_Checker/Proof_Checker.thy` now accepts a native
`TRS_Nontermination_Proof` for `AC_input R A C` when the claimed answer is NO.
It checks the proof for ordinary full rewriting by exactly R, without replacing
the certificate's AC input. The new lemma
`ordinary_nontermination_implies_ac_nontermination` proves the lift using
`rstep R ⊆ relation_ac_tp (R,A,C)` and `SN_subset`.
No assumptions, axioms, or unchecked proof imports are added. This is a sound
ordinary-to-modulo nontermination bridge, not a complete AC-loop processor.

## Verified build and executable

Tree/branch: `CeTA-consolidated`, `consolidated`, based on cfcbb50.
Changed theory SHA-256:
`402fdbea40a5d9bc37c270887b4440cfa03da7295d450360c286780eef634d56`.

Private build directory: `target/equational-production-20261019/`.
The corrected production run passed `Proof_Checker`, `Code`,
`RFC_Absolute_Ext`, and `Relative_ADP_Ceta_Dev`, with Isabelle2025-2,
`threads=8`, `parallel_proofs=0`, two session jobs, and private writable heaps.
The source snapshot and environment are recorded in
`corrected-source-identity.json` and `isabelle-corrected-build.receipt.json`.
Generated Haskell is compiled with GHC 9.6.7, `-O2 -package array -XRankNTypes`.

Use the integrated executable, not an ordinary-only replacement:

`target/equational-production-20261019/ceta-relative`

SHA-256: `3b807298addb1433df24dd6e60528ae5021b45fcc8b1a153957877abdaaad55f`.
`binaries.json` binds the executable hash to the corrected source identity and
successful build receipt. The previous pinned production binary is retained.

## Acceptance

- `compact-regression/summary.json`: 208 positive and 408 semantic-negative
  cases pass, each checked twice with original-input audits for positives.
  No HPC coverage run is claimed for this change.
- Ferrum `target/equational-20261018/final-new-checker-tests/`: four native AC
  YES proofs and two renamed native AC NO proofs pass twice; malformed proof
  obligations, empty-relation NO mutations, and lost-theory audits reject.
- Ferrum `target/equational-20261018/retained-10/`: all 71 original ETRS roots
  (67 YES, four NO) pass twice with original rules and A/C declarations audited.
  Fresh final-source NO regeneration also passes.

The first isolated build accidentally checked the unmodified archived source:
`git apply` discovered the enclosing repository and skipped the nested paths.
It is **not** extension-validation evidence. The snapshot was corrected, its
theory compared byte-for-byte with the edited source, and the complete affected
build repeated. The staging helper now limits Git repository discovery and
asserts changed-file equality before building; export additionally checks the
successful corrected receipt and the theory hash above.
