---
type: Formal Specification
title: "SRS Cycle: concrete NO checks and original-input boundary"
status: stable
---
# SRS Cycle review

The [published Cycle category](https://termination-portal.org/wiki/Cycle_Rewriting)
uses finite words modulo rotation. A step rotates to expose an occurrence of a
rule, performs one replacement, and may rotate the result. Rotations alone never
count as steps. The published prefix form, rotating to `l w` and replacing it
with `r w`, agrees with replacement in arbitrary string context: rotate `u l v`
to `l v u`, apply the rule, then rotate `r v u` to `u r v`.
For example, `ab -> ba` terminates on ordinary strings but loops on cycles.

Read [SRS_Spec_Base](../thys/Category_Specifications/Spec/SRS_Spec_Base.thy),
[SRS_Cycle_Spec](../thys/Category_Specifications/Spec/SRS_Cycle_Spec.thy),
[Cycle equivalence](../thys/Category_Specifications/Bridge/SRS_Cycle_Equivalence.thy),
then [Cycle checker bridge](../thys/Category_Specifications/Bridge/SRS_Cycle_Checker_Bridge.thy).
The canonical property excludes infinite sequences of explicit cycle steps.
Finite input lists supply finite rule sets. Empty words, empty left sides and
an empty alphabet are allowed. The examples include the empty system, a rotation
self-loop after replacement, and the empty-word self-loop.

## Exact theorem boundary

`cycle_string_step_iff` identifies the canonical single step with `cycle_step`.
`srs_cycle_terminates_iff` states, without extra hypotheses:

```
srs_cycle_terminates R <-> SN (cycle_step R)
```

`srs_cycle_nontermination_over_alphabet` states that, if both sides of every rule
contain only letters satisfying `P`, nontermination is equivalent to an infinite
cycle derivation whose every word contains only such letters. The proof erases
other letters and preserves every genuine step. This also works for the empty
alphabet; there is no nonempty-alphabet or unchecked extension assumption.

Each of `srs_cycle_transport_checker_NO`, `srs_cycle_embedding_checker_NO` and
`srs_cycle_morphism_checker_NO` concludes `not srs_cycle_terminates (set R)` from
acceptance by its corresponding concrete Boolean checker on the same rule list.
These checks have no certificate-assumption mechanism and no uninstantiated
checker-module contracts. No additional semantic guard remains for these NO
checks. The three families are not a complete nontermination procedure.

The unified Cycle adapter exposes **NO only**. There is no Cycle YES certificate
API or YES bridge. Ordinary SRS YES certificates cannot establish Cycle YES.
The Haskell `Read` parser and adapter are not Isabelle-verified serialized
parsing; this review does not describe them as a serialized soundness theorem.

## Original-input boundary

The [TPDB ARI repository](https://github.com/TermCOMP/TPDB-ARI/tree/master/SRS_Cycle)
uses unary `(format TRS)` inputs. Cycle semantics are requested explicitly by
`prove-cycle` or `cert check-cycle`; the ARI format alone does not distinguish
ordinary string rewriting from cycles. Any category path metadata must agree.
An ordinary TRS command rejects a path explicitly marked `SRS_Cycle`.

`ferrum cert check-cycle ORIGINAL.ari CANDIDATE.json PROOF.cycle --ceta CETA`
validates every declaration, including unused symbols, and requires unary rules
whose two sides share a tail variable. Unsupported strategy declarations, costs,
attributes and conflicting categories are rejected. It reconstructs the native
rule encoding, compares the actual certificate with the checked witness, and
invokes the unified checker explicitly with `--category cycle`. The receipt
records immutable source, candidate, certificate and checker identities.
The independent replay audit validates the same source rules separately and
checks every retained certificate twice, including an invalid-rule mutation.

Direct CeTA checks establish the property of the rules inside the certificate.
The bound command and replay audit additionally connect those rules to the
original file. The certificate format and generated checker code are unchanged.

## Verification and remaining trust

[Verification receipt](data/srs-cycle-review-20261108.json) records the normal
specification/bridge build, admission and oracle audits, input tests and replay.
The audited Cycle theorems have **no oracle dependencies**, including neither
`check_eqv` nor `cancel_type_definition`. No admissions or new axioms were added.
The Isabelle/HOL logical foundations, kernel and infrastructure remain trusted.

The remaining execution boundary includes ARI parsing, symbol encoding and
comparison, native certificate serialization, Haskell `Read` and category
dispatch, Isabelle code generation/export provenance, compilers, runtime,
artifact handling and hashes. These parts have tests and retained evidence,
not an end-to-end formal parser/compiler correctness proof.

All 200 protected Cycle NO roots pass fresh strict replay, original-input
binding, repeated checks and guidance authorization. There are no losses and
no oracle changes. All 254 category inputs pass both parser preflights; 27 Cycle
binding cases, 22 Rust parser tests, 14 Cycle tests and the earlier six categories'
82 binding cases pass. This is a focused Cycle replay, not a new combined
seven-category replay. Earlier combined six-category evidence is preserved.
CeTA's executable and generated logic are unchanged. No production promotion,
checker completeness, human approval or independent two-checker release is claimed.
