---
type: Formal Specification
title: "Conditional rewriting: ordinary and operational specifications"
status: draft
---
# Two Conditional properties

Ordinary termination excludes infinite sequences of completed conditional
rewrites. Operational termination additionally excludes infinite attempts to
evaluate conditions. These are separate category properties, not two spellings
of one checker mode. Ferrum's `TRS_Conditional` denotes the operational category;
`TRS_Conditional_Termination` denotes ordinary termination.

The [TPDB conventions](https://termination-portal.org/wiki/Term_Rewriting)
currently specify oriented conditions. Their description of the distinction
between the two categories is incomplete. The inference-system interpretation
and its relationship to order-based proofs are discussed in
[Schernhammer and Gramlich, 2009](https://www.logic.at/vmtl/opterm.pdf), building
on Lucas, Marche and Meseguer's operational semantics. A literature theorem is
not treated as an Isabelle theorem or an extra axiom in this package.

## Reading order and shared objects

1. [TRS_Spec_Base](../thys/Category_Specifications/Spec/TRS_Spec_Base.thy) defines the existing finite terms, ranked signatures, substitutions, one-hole contexts and Standard rewrite relation.
2. [Rewriting_Sequences_Spec](../thys/Category_Specifications/Spec/Rewriting_Sequences_Spec.thy) supplies finite sequences and absence of infinite sequences.
3. [TRS_Conditional_Spec_Base](../thys/Category_Specifications/Spec/TRS_Conditional_Spec_Base.thy) adds conditional rules and ordered inference goals, using those same terms and operations.
4. [Ordinary specification](../thys/Category_Specifications/Spec/TRS_Conditional_Ordinary_Spec.thy) defines `trs_conditional_terminates`.
5. [Operational specification](../thys/Category_Specifications/Spec/TRS_Conditional_Operational_Spec.thy) defines `trs_conditional_operationally_terminates`.
6. [Examples](../thys/Category_Specifications/Spec/TRS_Conditional_Examples.thy) distinguish the properties and relate unconditional rules to Standard rewriting.

There is no duplicated first-order term or context datatype. The new
`conditional_goal` datatype describes questions about the existing terms:
`CRewrite s t` asks for one step; `CReach s t` asks for a finite sequence.
The earlier Standard, Innermost, Relative, Context-sensitive and Outermost
specifications likewise use `TRS_Spec_Base`. SRS uses its shared word definitions;
higher-order rewriting uses its shared typed, binding-aware term definitions.
Those are distinct mathematical objects, not alternative first-order encodings.

## Canonical semantics

`conditional_problem A R` requires finite signature-correct rules and an
infinite variable type. Each rule contains a left side, a right side and an
ordered list of pairs whose interpretation is reachability. It does not silently
require determinism, nonvariable left sides, a constant symbol or restrictions
on extra variables. Checker-family restrictions must be proved or checked
separately, not inserted into this input predicate.

The inference rules are reflexive reachability, transitivity with a rewrite
first, and a rule instance in an arbitrary context whose premises are its
instantiated conditions in order. All instances respect the ranked signature.
`conditional_success` is the least inductive closure of these rules: every
premise must have a finite successful derivation. Circular reasoning cannot
establish a rewrite step.

`conditional_evaluation_step` descends from a goal into one of an inference
rule's premises only when every earlier premise has succeeded. The selected
premise need not succeed. An infinite sequence of these descents represents
an infinite branch of a left-to-right proof attempt. This definition does not
mention quasi-decreasingness or any checker implementation.

The ordinary property excludes infinite sequences of successful `CRewrite`
goals. The operational property excludes infinite evaluation branches. Both
specifications expose nontermination as an existential infinite sequence.
`operational_implies_ordinary` proves the implication between the two properties.

The rule `a -> b if a ->* b`, with distinct constants, supplies the strict
counterexample: there are no successful rewrites, but condition evaluation
repeats forever. Both claims are proved. Further examples cover empty ordinary and operational termination, a
nonground loop over a signature without constants, a terminating guarded
reduction below the root, and rejection of arity-mismatched starts. `unconditional_step_iff` proves that removing all
conditions gives exactly the shared Standard relation, not a second definition
of unconditional rewriting.

## Review status and remaining obligations

Build all three sessions with `make isabelle-conditional-integrated`.
The specifications and examples compile independently in the lightweight
`Category_Specifications` session. No human approval is implied by a build.
The separate Conditional review now connects both properties to concrete YES
and NO checking. Human approval of the mathematical specification remains
separate from the machine-checked proof and replay gates.

## Exact representation and checker connections

[Ranked equivalence](../thys/Category_Specifications/Conditional_Bridge/TRS_Conditional_Ranked.thy)
uses the existing term, substitution and context bijections. Conditional-rule
translation preserves condition order. `conditional_inference_iff`,
`conditional_success_iff`, `conditional_step_iff_ranked` and
`conditional_evaluation_iff_ranked` prove preservation and reflection.
The two exact termination statements are:

```
trs_conditional_terminates A R =
  SN (ranked_cstep (to_signature A) (to_conditional_rules R))

trs_conditional_operationally_terminates A R =
  SN (ranked_conditional_evaluation (to_signature A) (to_conditional_rules R))
```

Negating either equality gives the corresponding nontermination equivalence.
The native ranked relations enforce the signature at every inference and
substitution. They are not silently replaced by unrestricted library `cstep`.
The [embedding](../thys/Category_Specifications/Conditional_Bridge/TRS_Conditional_Embedding.thy)
proves that unrestricted ordinary termination suffices for the ranked ordinary
property. The [operational transfer](../thys/Category_Specifications/Conditional_Bridge/TRS_Conditional_Operational_Transfer.thy)
proves that a quasi-decreasing order excludes infinite canonical evaluation.
Neither soundness argument needs an unproved signature-extension theorem.

The [YES bridge](../thys/Category_Specifications/Conditional_Integrated/TRS_Conditional_Checker_Bridge.thy)
provides concrete and serialized ordinary and operational corollaries. Ordinary
checking uses the existing integrated CTRS termination result, or the separate
condition-erasure checker. Operational YES uses the actual quasi-reductive
unraveling proof. Certificate assumptions are disabled; the concrete checker
module contracts are proved. Erasure alone is rejected for operational YES.

The [ordinary NO bridge](../thys/Category_Specifications/Conditional_Integrated/TRS_Conditional_NO_Bridge.thy)
proves `conditional_checked_ordinary_NO`. Its premises are accepted native
rewrite-loop checking, exact rules, finite signature guards, at least one
rewrite, and signature-correct loop substitution images. Argument steps
accumulate a context. Checked nested condition proofs are reflected into ranked
successful derivations; the resulting contextual substitution loop supplies an
infinite ranked rewrite sequence.

The [operational NO bridge](../thys/Category_Specifications/Conditional_Integrated/TRS_Conditional_Operational_NO.thy)
provides `conditional_checked_rewrite_loop_operational_NO` and
`conditional_checked_operational_call_cycle_NO`. The first uses the proved
implication from operational to ordinary termination. The second translates a
checked call cycle into a closed positive evaluation path. Earlier conditions
must have checked successful proofs; the selected condition need not succeed.
Argument contexts are accumulated and each call resets the evaluation target.
The binder rotates a call cycle to end in a call and checks the rotated witness
again. `evaluation_environment_last_call` proves closure by construction.
This does not identify failure of quasi-decreasingness with operational
nontermination by assumption, and does not require a determinism hypothesis
for the direct cycle argument.

## Strict input boundary and coverage

[Ferrum's binding and replay review](../../ferrum/docs/conditional-certification-boundary.md)
describes the two explicit CLI properties. Both use the TPDB Conditional corpus;
ordinary versus operational is never inferred from its common source path.
The ARI reader validates every declaration, arity, format and condition. It
preserves unused declarations and permits empty systems and variable left sides.
The binder checks original rules, condition order, shared variables, answer and
proof family. Native rule indices, positions, substitution images and recursively
nested condition witnesses must respect the declared signature. These finite
checks discharge the NO theorem guards; they are not unproved semantic contracts.

The reviewed NO families are rewrite-only cycles and substitution loops for
both properties, plus condition-call cycles for operational termination.
Call-containing loops with a nonempty substitution are rejected at this boundary.
Such a limitation produces no accepted answer; it is a coverage restriction.
It excludes none of the retained Conditional witnesses. The checker may impose
additional checked applicability restrictions on a particular proof family,
without adding them to the canonical category definition.

Fresh strict replay and final packaging retain **122/122 operational roots
(84 YES, 38 NO)** and **117/117 ordinary roots (92 YES, 25 NO)**. Both use the
same immutable unified CeTA executable. Six additive guidance keys repair four
roots with unused declarations and two innermost child-state serializations.
The failed replay remains preserved. This is a focused two-property gate, not a
new combined replay of all earlier categories or a completeness claim.

## Remaining trust boundary

There are no open semantic-equivalence, signature-extension or checker-module
premises in these reviewed YES/NO paths. The input-domain conventions remain
finite signature-correct rules and an infinite variable supply. Finite witness
checks and proof-family coverage restrictions are explicit above.

Trust still includes Isabelle/HOL and its kernel, the inherited
`Regexp_Method.check_eqv` and `Types_To_Sets.cancel_type_definition` mechanisms
in the existing YES dependency chain, code generation, the Haskell compiler and
runtime, native ARI/CPF/Haskell parsing, the Rust correspondence/normalization
code, and executable/artifact identity. Native parsing and dispatch are tested,
not proved correct in HOL. Checking the human specification establishes the
meaning of the soundness conclusions; it does not make the prover or checker
complete. The ranked/NO theorem audit reports no oracle dependencies. No new axiom or admitted proof is introduced. Generated checking
logic, certificate formats and the unified executable remain unchanged.

Build, oracle-dependency and source-hash evidence is recorded in the
[completed review receipt](data/conditional-review-20261108.json); the earlier
[specification milestone](data/conditional-specifications-20261108.json) remains
historical evidence. Next in the review order is TRS Equational.
