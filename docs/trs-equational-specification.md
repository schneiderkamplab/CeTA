---
type: Formal Specification
title: "TRS Equational: ranked specification and checker boundary"
status: draft
---
# TRS Equational

The [TPDB category definition](https://termination-portal.org/wiki/Term_Rewriting#TRS_Equational)
uses unrestricted rewriting modulo separately declared associativity and
commutativity. A binary symbol may carry A, C or both. Terms and substitutions
may be nonground; rule validity imposes no variable-left-side or extra-variable
restriction. Costs and strategy declarations are not part of this category.

## Reading order

1. [TRS_Spec_Base](../thys/Category_Specifications/Spec/TRS_Spec_Base.thy) defines the shared finite terms, ranked signatures, substitutions, contexts and ordinary rewrite steps.
2. [Rewriting_Sequences_Spec](../thys/Category_Specifications/Spec/Rewriting_Sequences_Spec.thy) defines finite sequences and absence of infinite sequences.
3. [TRS_Equational_Spec](../thys/Category_Specifications/Spec/TRS_Equational_Spec.thy) defines the category property using those same objects.
4. [Examples](../thys/Category_Specifications/Spec/TRS_Equational_Examples.thy) cover empty rules, equation-only conversions, a decreasing rule, a modulo loop, below-root nonground rewriting, a constant-free signature and arity errors.
5. [Equivalence](../thys/Category_Specifications/Equational_Bridge/TRS_Equational_Equivalence.thy) and [concrete checker bridge](../thys/Category_Specifications/Equational_Integrated/TRS_Equational_Checker_Bridge.thy) establish the machine-checked correspondence.

The lightweight specification imports no checker or IsaFoR rewriting theory.
`equational_problem A R FA FC` requires finite signature-correct input rules,
an infinite variable type, finite theory declarations and arity two for every
theory symbol. The signature need not have constants. The equation-instance
set is infinite in general: it describes the theory, not additional input rules.

## Canonical property and exact correspondence

`equational_axioms FA FC` contains both directions of associativity and all
commutativity instances. `equational_conversion` is a finite sequence of the
shared ranked rewrite steps using these equations. One `equational_step`
consists of an equation conversion, one strict input-rule step, then another
equation conversion. `trs_equational_terminates` excludes an infinite sequence
of these steps. Infinite equation changes alone do not violate the property.
`trs_equational_nontermination_iff` exposes the corresponding infinite sequence.

The bridge reuses the existing term, substitution, context, signature and rule
translations. `equational_axioms_translation` identifies the translated theory
with IsaFoR's `AC_trs FA FC`. `equational_step_iff_ranked` proves preservation
and reflection of individual steps. With `F = to_signature A`, the exact
termination theorem `trs_equational_terminates_iff_ranked` states:

```
trs_equational_terminates A R FA FC =
  SN_rel (sig_step F (rstep (to_rules R)))
         (sig_step F (acrstep FA FC))
```

`trs_equational_nonterminates_iff_ranked` is its negation. These representation
equivalences have no extra hypotheses. `equational_unrestricted_relation`
identifies the native modulo relation with `relto (rstep R) (acrstep FA FC)`.
`equational_termination_transfer` proves that unrestricted native termination
implies the canonical ranked property. We do not assert a general unrestricted
signature-extension equivalence for rewriting modulo equations.

## Actual YES and NO dispatch

`trs_equational_integrated_YES` assumes exact translated rules, exact A/C sets,
and acceptance of `AC_input Rs As Cs`, `Termination`, `Decision True`, with
certificate assumptions disabled (`False`). Its conclusion is the canonical
property. Concrete integrated module correctness is proved by the existing
checker, rather than exposed as an unchecked module premise.

`trs_equational_integrated_NO` assumes `equational_problem`, exact translated
rules, and assumption-free acceptance on that AC input of
`Inl (TRS_Nontermination_Proof p)`, `Termination`, `Decision False`. Its conclusion
is the negation of the canonical property. This is CeTA's actual Equational NO
dispatch: an ordinary nontermination proof on the same strict rules. The bridge
proves equality with Standard checking, applies Standard's proved ranked
signature transfer, and includes each ordinary step in modulo rewriting.
Ordinary nontermination works for any declared theory; the executable binder
nevertheless requires the original A and C declarations to match exactly.
No new witness-signature condition or unproved modulo signature extension is
needed. This does not claim a checker for arbitrary modulo-only NO witnesses.

`trs_equational_serialized_YES` and `trs_equational_serialized_NO` additionally
state the exact result of `parse_combined_integrated_cert_problem None None None`
and assumption-free acceptance of the same text. Parsing correspondence is an
explicit boundary, discharged operationally by the strict source binder; it is
not a proved ARI/XML parser theorem.

## Verification and remaining trust

Build the separate sessions with `make isabelle-equational-integrated`.
The [review evidence](data/equational-review-20261108.json) records the successful
build, proof-dependency audit and exact source snapshot at commit `985dbe6`
on CeTA `main`. The specification and
examples compile in the lightweight HOL session. Human approval remains pending.

The [Ferrum boundary review](../../ferrum/docs/equational-certification-boundary.md)
records strict declaration, signature, rules, answer and CPF-kind binding,
and fresh protected replay: 71/71, comprising 67 YES and four NO. No unchecked
semantic or checker-module hypothesis remains in these reviewed paths.
Soundness does not imply checker or prover completeness.

The equivalence audit reports no oracle dependencies. The joint concrete and
serialized checker audit reports only the inherited `Regexp_Method.check_eqv`
and `Types_To_Sets.cancel_type_definition` mechanisms. All audited theorems
pass `Thm_Deps.has_skip_proof` checks without admissions.

Remaining trust includes Isabelle/HOL and its kernel, those inherited oracle
mechanisms, code generation, Haskell
compilation/runtime, native parsing, Rust source binding, dispatch and artifact
identity. Native parser and executable correspondence are tested, not proved
in HOL. No certificate format, generated checking logic or production executable
changes in this review.
