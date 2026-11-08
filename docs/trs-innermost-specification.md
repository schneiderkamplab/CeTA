---
type: Formal Specification
title: "Ranked TRS Innermost: specification and semantic correspondence"
status: draft
---
# Ranked TRS Innermost

Read the [shared base](../thys/Category_Specifications/Spec/TRS_Spec_Base.thy),
then [TRS_Innermost_Spec](../thys/Category_Specifications/Spec/TRS_Innermost_Spec.thy),
[examples](../thys/Category_Specifications/Spec/TRS_Innermost_Examples.thy),
[equivalence](../thys/Category_Specifications/Bridge/TRS_Innermost_Equivalence.thy),
and [checker bridge](../thys/Category_Specifications/Bridge/TRS_Innermost_Checker_Bridge.thy).

A step contracts a rule instance in an arbitrary context, provided every proper
subterm of that instance is irreducible. Irreducibility means no instance of any
left side occurs anywhere in the term. Other branches may contain redexes;
there is no left-to-right strategy. Substitutions can be nonground.

`standard_problem A R` requires infinitely many variables, finitely many rules
and signature-correct rule sides. Variable left sides and extra right variables
are allowed. Signatures need not contain constants. `trs_innermost_terminates`
is absence of an infinite sequence of these steps. Input validity is separate.
Its negation is exposed by `trs_innermost_nontermination_iff`.

## Correspondence statements

- `normal_iff_no_standard_step`: on a valid problem and a signature-correct
  term, irreducibility is exactly absence of an ordinary step.
- `normal_iff`: for a signature-correct term, irreducibility iff its translation
  belongs to `NF_terms (lhss (to_rules R))`.
- `innermost_step_iff`: the canonical step iff the translated pair belongs to
  `sig_step (to_signature A) (irstep False (to_rules R))`.
- `trs_innermost_terminates_iff_signature`: the canonical property iff
  `SN (sig_step (to_signature A) (irstep False (to_rules R)))`.
- `trs_innermost_terminates_iff_injection`: assuming a valid problem and an
  injection from IsaFoR terms into variables, the canonical property iff
  `SN (irstep False (to_rules R))`.
- `trs_innermost_terminates_iff`: discharges that injection for countable
  symbols and countably infinite variables. The infinite-variable assumption
  comes from `standard_problem`; no additional rule restrictions are imposed.
- `trs_innermost_terminates_iff_on`: under those same assumptions, equivalence
  with `SN_on` on signature-correct initial terms.
- `trs_innermost_nonterminates_iff`: the negated global equivalence.

The specification and signature-restricted equivalence have no countability
restriction. Countability is an explicit assumption of this signature-extension
proof, and holds for CeTA's symbol names and string variables.

`trs_innermost_checker_YES` and `trs_innermost_checker_NO` conclude the canonical
property and its negation respectively. Both assume a valid problem,
`tp_spec I`, `dpp_spec J`, `tp_ops.nfs I tp = False`,
`set (tp_ops.Q I tp) = lhss (to_rules R)`,
`set (tp_ops.R I tp) = to_rules R`, and `tp_ops.Rw I tp = []`.
The symbol parameter has classes `countable`, `compare_order` and `showl`;
variables are strings. Acceptance is respectively
`isOK (check_trs_termination_proof I J False i tp prf)` or
`isOK (check_trs_nontermination_proof I J False i tp prf)`.

The `False` certificate argument forbids assumptions. The `nfs = False` field
is the default Innermost configuration: proper redex subterms must be normal,
but the checker does not impose a separate normality restriction on all
substitution images. See the [package page](category-specifications.md) for
build status and the boundary of the claims.

## Strict concrete bridge

The [completed concrete review](trs-innermost-trust-boundary.md) composes the
integrated checker with this specification. Its YES/NO corollaries discharge
the abstract module contracts above. Bound runtime paths require explicit
`nfs=false`, no weak rules and exact original-input correspondence; omitted or
true flags are rejected. See that review for exact premises and remaining trust.
