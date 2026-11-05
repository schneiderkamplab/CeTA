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
- The complete integrated export is still rebuilding. Evidence is retained in
  `target/rfc-recursive-build-1.log` in the isolated `CeTA-policy-eval` checkout.
- Regenerated unified executable, repeated nested positive certificates,
  semantic mutations, historical compatibility and category replay are
  pending. This page does not claim those gates have passed.
