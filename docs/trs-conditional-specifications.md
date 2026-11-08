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
The implementation is **not yet a completed Conditional category review**.

The [separate bridge](../thys/Category_Specifications/Conditional_Bridge/TRS_Conditional_Embedding.thy) reuses the existing term, substitution and context
translations. Its additional translation preserves the order of conditions.
`conditional_success_embedding` transfers successful finite derivations to
IsaFoR conditional rewriting. `conditional_ordinary_termination_transfer`
transfers ordinary termination in the sound direction. These are embeddings,
not a claim of full ranked equivalence.

The [operational transfer](../thys/Category_Specifications/Conditional_Bridge/TRS_Conditional_Operational_Transfer.thy) connects a quasi-decreasing order to the actual
proof-attempt definition using a lexicographic order on a goal's source term
and its phase. The [concrete YES bridge](../thys/Category_Specifications/Conditional_Integrated/TRS_Conditional_Checker_Bridge.thy) distinguishes common-checker ordinary
termination, quasi-reductive operational termination, and ordinary-only
condition erasure. Certificate assumptions are disabled and concrete module
contracts are instantiated. Build and oracle evidence is recorded in the
[receipt](data/conditional-specifications-20261108.json).

Outstanding work includes reflection and exact ranked equivalences, both
canonical NO connections, strict source/signature/property binding for both
serialized formats, all native parser and dispatch checks, and fresh protected
replay. In particular, an ordinary-only erasure proof must not be accepted for
operational termination, and a condition-call loop must not establish ordinary
nontermination. The existing native NO theorem's conclusion about
quasi-decreasingness is not silently identified with the new operational spec.

Native ARI and certificate parsing, executable provenance, code generation,
compiler/runtime and inherited Isabelle mechanisms remain outside the new
specifications. No generated checker, certificate format, production binary
or oracle changes are part of this specification milestone.
