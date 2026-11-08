---
type: Formal Specification
title: "Higher-order rewriting: specification and checker boundary"
status: draft
---
# Higher-order rewriting review

The category is simply typed curried rewriting in union with beta reduction,
with arity-aware meta-substitution. The authoritative syntax and semantics are
in the [TermCOMP reference](https://github.com/TermCOMP/termcomp-reference/blob/d41b97e833b11e1770afd43c73ed53ac9017742f/stcrs.tex).
This is not rewriting with arbitrary matching modulo beta or eta.

Read [the shared typed definitions](../thys/Category_Specifications/Spec/Higher_Order_Spec_Base.thy),
[the ambient category property](../thys/Category_Specifications/Spec/Higher_Order_Spec.thy),
[the declared-sort property](../thys/Category_Specifications/Spec/Higher_Order_Sorts_Spec.thy),
[examples](../thys/Category_Specifications/Spec/Higher_Order_Examples.thy),
[the equivalence](../thys/Category_Specifications/Higher_Order_Bridge/Higher_Order_Equivalence.thy),
then [the concrete checker bridge](../thys/Category_Specifications/Higher_Order_Integrated/Higher_Order_Checker_Bridge.thy).
The standalone specification imports only the shared specification and HOL.
The separate sessions are `Category_Specifications`,
`Category_Higher_Order_Bridge` and `Category_Higher_Order_Integrated`.

## Mathematical conventions

Types are base sorts and arrows; terms have constants, free variables,
applications and abstractions. De Bruijn indices represent bound variables.
Rule meta-variables are distinct from term variables. Substitution lifts indices
to avoid capture and contracts only designated meta-arguments. Additional
ordinary applications remain explicit. Beta contraction is a separate step,
and either kind of step is allowed under application and abstraction.

`higher_order_problem S R` requires finite typed rules, constant-headed left
sides, beta-normal patterns, distinct bound arguments of left meta-variables,
a fixed left arity for each meta-variable, and no new right meta-variables.
Right occurrences supply the designated arguments and may have additional
ordinary arguments. A finite list gives the constant signature and rule list.
The source parser additionally binds every base sort to its declaration.

`higher_order_terminates S R` excludes an infinite sequence at every result
type and every finite free-variable typing environment. It concerns arbitrary
typed terms, including open terms and terms of functional type. It is not a
ground-term property. Nontermination is its negation; the specification lemma
`higher_order_nontermination_iff` exposes the infinite sequence.

## Exact connections

`higher_step_iff` and `higher_order_step_iff` preserve and reflect individual
steps under explicit bijections of types, terms, patterns and rules.
`higher_order_terminates_iff` states:

```
higher_order_terminates S R <->
  (forall V A. wf ((ho_relation (map to_ho_type S) V
                    (map to_ho_rule R) A)^-1))
```

`higher_order_nonterminates_iff` gives the corresponding existential failure
of well-foundedness. These equivalences have no extra semantic hypotheses.
They hold even beyond the valid category inputs; category validity is stated
separately, rather than assumed as an unproved checker contract.

The concrete bridge has sixteen YES corollaries and four NO corollaries.
Each YES premise is acceptance by the named concrete Boolean checker on the
translated signature and rules; its conclusion is `higher_order_terminates S R`.
The NO families are loop, embedding, plain pumping and rule pumping; each
concludes `not higher_order_terminates S R` from its concrete check.
The three delegated YES families use the concrete CPF XML checker soundness
results, including the actual processor implementations and assumption-free
checking. There are no open checker-module premises in these corollaries.
This establishes soundness, not completeness of proof search or certificates.

## Exact declared-sort correspondence

For an ARI source declaring `N` sorts, the final property is
`higher_order_terminates_over_sorts N S R`. Its terms, variable environments
and result types use only sorts below `N`. The lemma
`higher_order_declared_nontermination_iff` exposes the infinite sequence within
that universe. `higher_order_declared_problem` states the finite typed category
validity conditions, including declared sorts in every rule and constant type.
With no sorts there are no typed rules.

The [sort extension proof](../thys/Category_Specifications/Higher_Order_Bridge/Higher_Order_Sort_Extension.thy)
projects every undeclared sort to a declared sort, preserving typing,
substitution and every rewrite step. The integrated theorem
`higher_order_declared_sorts_iff` proves, for a valid declared problem:

```
higher_order_terminates_over_sorts N S R <-> higher_order_terminates S R
```

It also handles zero sorts, using the empty-rule termination theorem. Thus no
unproved sort-extension premise remains. Every checker corollary has a
`_declared_sorts` version. YES needs only concrete checker acceptance; NO also
states category validity for the same declared source. These are input validity
conditions checked by the source parser, not open checker contracts. The outer
parser-to-specification correspondence remains tested software.

The bound ARI interface requires at least one declared sort and rejects a file
with none; this is a parser coverage restriction, not a termination assumption.
The mathematics covers the empty-sort case as well. A declared sort without
constants is accepted, and open terms remain in scope.

## Original input and remaining trust boundary

Ferrum's `cert check-higher-order` parses the original ARI file, compares the
entire typed signature and ordered rule representation with the native
certificate, checks the requested answer against its proof family, and invokes
the unified CeTA executable with explicit category dispatch. Declared strategies
outside this unrestricted category, unknown declarations, malformed identifiers,
type errors and incompatible source paths are rejected. Witness types must use
declared sorts. A delegated proof requires its child CPF; ordinary native proofs
reject an extraneous child. Private snapshots and before/after hashes bind the
checked source, native certificate, child and checker identities.

The outer ARI/native-certificate parsing and this executable binding are tested
software, not proved parsers. The handwritten Haskell native adapter, generated
code compilation and runtime, filesystem/process boundary, and the usual
Isabelle/HOL foundations remain trusted. The child CPF connection is stronger:
its concrete XML acceptance theorem is part of the formal bridge. Replay is
additional evidence and does not prove parser correctness or search completeness.

## Verification and oracle audit

The three named sessions pass normal Isabelle builds with `quick_and_dirty`
disabled. The bridge explicitly audits all equivalences and all twenty concrete
corollaries and their declared-sort counterparts for skipped proofs. The dependency audit reports exactly
`Regexp_Method.check_eqv` and `Types_To_Sets.cancel_type_definition`, inherited
through the existing concrete checker proofs. No new axiom or oracle was added.
These mechanisms are part of the proof trust boundary; “no open semantic
premises” does not mean an oracle-free proof dependency graph.

The retained official reference is revision
`d41b97e833b11e1770afd43c73ed53ac9017742f`; its `stcrs.tex` SHA-256 is
`a7bade09db139e537253e4c0096414fddc7592876ba919e1a3d4a5fcd2068161`.

The [formal verification receipt](data/higher-order-formal-review-20261108.json)
pins the reviewed sources, build logs and dependency audit.

The [declared-sort verification receipt](data/higher-order-sorts-review-20261108.json)
adds the finite-sort equivalence, legal-substitution projection, all declared-sort
corollaries and their final build/oracle audit. The fresh executable replay is
recorded in the [Ferrum review](../../ferrum/docs/higher-order-certification-boundary.md).
