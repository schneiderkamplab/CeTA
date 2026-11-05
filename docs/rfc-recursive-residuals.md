---
type: Implementation Plan
title: "Recursive RFC residual checking"
status: draft
---
# Recursive RFC residual checking

The common termination-proof checker now distinguishes
`rfcMatchboxAbsoluteBounds` from `rfcMatchboxRelativeBounds` explicitly.
The former requests full termination of the retained rules. The latter
requests relative termination with the deleted rules weak. Their common
applicability checks still require full rewriting, empty Q, no existing weak
rules, the required linearity and language conditions, and a checked bounds
automaton.

The absolute constructor recurses through `check_trs_termination_proof`, just
like reversal, tiling and rule removal. Its child may therefore use any
constructor applicable to the resulting typed obligation. Parents likewise
retain this interpretation when they recurse. No special root dispatch is
needed for newly emitted absolute certificates. The old root-level wrapper is
retained to read historical artifacts that used the relative tag for absolute
continuations; its limited recursion is not the interface for new proofs.

`RFC_Checker_Ext/RFC_Absolute_Residual_Core.thy` makes the existing absolute
residual theorem available before the common checker. The old
`RFC_Absolute_Ext/RFC_Absolute_Residual.thy` remains as a compatibility import.
`Proof_Checker_Base/Check_Termination.thy` adds the constructor, recursive
assumption accounting and a soundness case. `CPF_Proof_Parser.thy` parses the
explicit tag. All changes are Isabelle sources; generated checking logic is
not hand-edited.

The authoritative [processor contract](../../ferrum/docs/processor-contract.md)
requires residual composition with checked parent reconstruction. A successful
child of the wrong property or context must still be rejected; arbitrary
syntactic nesting does not waive applicability conditions.

## Gates

- The updated common soundness proof and parser pass `Proof_Checker_Base` and
  `Proof_Checker`; the legacy wrapper also passes `RFC_Absolute_Ext`.
- The complete `Certificate_Performance_CPF_Export` build passes in
  `target/rfc-recursive-build-1.log` (48m08s including dependencies).
- The unified O2 executable has SHA-256
  `9dfd140cac92e7f47646b7d620848533c64beff7cbb2d7881cfe2df1298a1fdb`.
  Its generated CPF archive comes from source `3172b10`; other category
  archive identities remain unchanged. No generated logic was edited.
- `tests/unified/check_rfc_recursive.py` accepts the nested positive twice
  and rejects missing initial language, missing removal, invalid bound and
  changed-input self-loop mutations. The native source correspondence audit
  also passes in Ferrum's `target/policy-v37/nesting-control/checks.json`.
- Existing sparse tiling/removal positives and mutations, unified dispatch,
  CSR composition, GM04 source-map and retained semantic-negative gates pass
  in `target/rfc-recursive-existing-paths-1/results.json`.
- Ferrum's 34 focused RFC tests pass with this checker, including the updated
  reconstruction/serialization test. One unrelated bound-expectation test
  remains excluded after its failure was reproduced on the prior baseline.
- Fresh category replay and full-frontier release validation remain pending.

The [recorded gate identities](data/rfc-recursive-20261105.json) bind the
source, generated export and executable to these focused checks. This is a
verified integration candidate, not a promotion of the production checker.


## Exact duplicate-tail refinement

The final-state list may repeat the same state for distinct initial words.
The universal right-extension condition depends only on its set of states.
`rfc_right_distinct_tails_code` in `Certificate_Performance_CPF_Export` proves
that deduplicating this list preserves the executable result exactly. It does
not deduplicate the paired initial-language records or skip their checks.
The theorem is kernel checked, with an explicit no-oracles/admissions audit.

The complete export passes in `target/rfc-distinct-build-2.log` (6m20s).
Attempt one retains a fixed-variable name collision, corrected before proof
checking. Source `39f3374` generates the unified O2 checker
`d19704667ae17f6f6154d8b729e800a0ee15cfac416d26779534779c26062113`.
All focused nested, sparse, CSR, dispatch and negative regression gates pass.
[Export and gate evidence](data/rfc-distinct-tails-20261105.json).
Large-certificate timing tests and the full SRS replay remain in Ferrum's
`target/policy-v37`; this refinement alone is not a claim that every certificate
fits the competition checker deadline.
