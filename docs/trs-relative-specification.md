---
type: Formal Specification
title: "Ranked TRS Relative: specification and semantic correspondence"
status: draft
---

The definition-only package is separate from [derived properties](../thys/Category_Properties/TRS_Relative_Properties.thy)
and examples. See the [current package guide](category-specifications.md) for the three-layer layout.
# Ranked TRS Relative

Read the [shared package](category-specifications.md), then the
[specification](../thys/Category_Specifications/TRS_Relative_Spec.thy),
[examples](../thys/Category_Properties/TRS_Relative_Examples.thy),
[equivalence](../thys/Category_Bridges/Bridge/TRS_Relative_Equivalence.thy)
and [checker bridge](../thys/Category_Bridges/Bridge/TRS_Relative_Checker_Bridge.thy).

A relative block consists of finitely many weak steps, one strict step and
finitely many weak steps. `trs_relative_terminates A R S` excludes an infinite
sequence of such blocks. Infinite weak-only sequences are permitted.
`relative_problem A R S` requires both finite rule collections to satisfy the
shared ranked problem predicate; it adds no variable condition.

`relative_step_iff` identifies one block with IsaFoR's `relto` of the two
signature-restricted rewrite relations. `trs_relative_terminates_iff_signature`
identifies the canonical property with `SN_rel` of those relations. Both
statements are unconditional. `trs_relative_nontermination_iff` exposes the
infinite sequence defining nontermination.

## Signature extension is conditional

Unlike Standard, relative termination is not invariant under arbitrary
signature extension. The existing library proves counterexamples in
`sig_ext_relative_rewriting_unsound`. The bridge predicate
`relative_extension_condition A S` requires either a symbol in `A` of arity
greater than one, or that each weak rule's right-side variables occur on its
left side. These conditions are sufficient; they are not asserted necessary
for each individual problem.

`trs_relative_terminates_iff` assumes `relative_problem A R S` and
`relative_extension_condition A S`, and concludes equivalence with
`SN_rel (rstep (to_rules R)) (rstep (to_rules S))`.
`trs_relative_nonterminates_iff` gives its negation.
`ordinary_relative_implies_ranked` needs no extension condition.

## Checker corollaries

Both corollaries assume `relative_problem A R S`, `tp_spec I`, `dpp_spec J`,
`tp_ops.nfs I tp = False`, `tp_ops.Q I tp = []`,
`set (tp_ops.R I tp) = to_rules R` and
`set (tp_ops.Rw I tp) = to_rules S`.

`trs_relative_checker_YES` additionally assumes
`isOK (check_trs_termination_proof I J False i tp prf)` and concludes
`trs_relative_terminates A R S`. It needs no extension condition.

`trs_relative_checker_NO` additionally assumes
`relative_extension_condition A S` and
`isOK (check_reltrs_nontermination_proof I J False i tp prf)`, and concludes
`not trs_relative_terminates A R S`. It uses the relative nontermination
checker, not the ordinary nontermination checker. Both calls forbid certificate
assumptions. These are semantic input statements, not parser claims.

The focused proof check, including the inherited-admission audit, has passed.
Normal package integration also passed; see the
[verification receipt](data/category-specifications-relative-strings-20261107.json).

## Concrete review update

The [ranked input and concrete checker review](trs-relative-trust-boundary.md)
retains the conditional equivalence above and adds guarded bound acceptance.
YES requires no extension condition. NO now passes either the runtime extension
guard or a direct ranked-loop check, proved without signature extension.
No extra variable restriction is imposed on category validity. Other unrestricted
NO families still require the sufficient extension condition. Accepted decisions
use the canonical property; this does not claim certificate completeness.
