---
type: Formal Specification
title: "TRS Outermost: specification and checker boundary"
status: draft
---
# TRS Outermost review

The [TPDB category definition](https://termination-portal.org/wiki/TRS_Outermost)
permits a rewrite precisely when no strict ancestor of its position is a redex.
Termination quantifies over every such sequence. There is no left-to-right
selection, fairness requirement or restriction to ground terms. The general
[term-rewriting conventions](https://termination-portal.org/wiki/Term_Rewriting)
allow arbitrary term pairs, including variable left sides and extra right-side
variables. Left-linearity is not a category requirement.

## Reading order and conventions

Read the [shared terms and signatures](../thys/Category_Specifications/Spec/TRS_Spec_Base.thy),
[Outermost specification](../thys/Category_Specifications/Spec/TRS_Outermost_Spec.thy),
[examples](../thys/Category_Specifications/Spec/TRS_Outermost_Examples.thy),
[equivalence](../thys/Category_Specifications/Outermost_Bridge/TRS_Outermost_Equivalence.thy),
[finite loop bridge](../thys/Category_Specifications/Outermost_Bridge/TRS_Outermost_Loop_Bridge.thy),
then the [concrete and serialized checker bridge](../thys/Category_Specifications/Outermost_Integrated/TRS_Outermost_Integrated.thy).
The standalone specification imports only shared specifications and HOL.

A ranked signature assigns each permitted symbol one arity. Terms are finite
first-order trees; substitutions map variables to signature-correct terms.
`standard_problem A R` requires finite signature-correct rule pairs and an
infinite variable supply. It does not require a constant symbol. Contexts have
one hole. `outermost_above` checks each strict ancestor of that hole for absence
of a matching rule left side. `outermost_step` contracts one rule instance in
such a context, with signature-correct endpoints.

`trs_outermost_terminates A R` is the absence of an infinite sequence of these
steps. `trs_outermost_nontermination_iff` exposes the corresponding infinite
sequence. Examples include empty rules, a terminating reduction, self-loops,
blocked and permitted below-root reductions, nonground substitutions, variable
left sides, arity mismatch and signatures without constants.

## Exact theorem boundary

`outermost_step_iff` preserves and reflects steps under the shared explicit
term, substitution, context and rule translations. It has no extra hypotheses.
`trs_outermost_terminates_iff_signature` states:

```
trs_outermost_terminates A R <->
  SN (sig_step (to_signature A)
       (ostep (fst ` to_rules R) (to_rules R)))
```

`trs_outermost_nonterminates_iff_signature` gives the negated equivalence.
The signature restriction is intentional. Existing unrestricted Outermost
signature-extension results require well-formed rules and quasi-left-linearity;
those are not assumptions of this category and are not imposed on its spec.

`trs_outermost_integrated_YES` requires exact translated rules and acceptance
by `certify_integrated_cert_problem False` of an Outermost termination claim.
It concludes the canonical property, for every concrete integrated YES proof
family. Restricting the checker's terminating relation to the declared signature
needs no extra assumption. Concrete module contracts are discharged.

`trs_outermost_integrated_NO` uses the same exact rules and assumption-free
acceptance of a **direct loop** certificate. Its finite witness premises require
all symbols and arities in the start term, sequence result terms, substitution
images and loop context to belong to the declared signature. The loop bridge
proves that every iteration stays in that signature and gives an infinite
Outermost sequence there. These premises are checked by the bound runtime
interface; they are not assumed signature-extension principles. No rule-shape,
left-linearity, groundness or constant-symbol hypothesis is added.

`trs_outermost_serialized_YES` and `trs_outermost_serialized_NO` compose those
results with `parse_combined_integrated_cert_problem None None None` and
`certify_proof_integrated False None None None`. Exact parsed input and the NO
witness checks remain explicit. There are no abstract checker-module premises.

The bound NO interface currently accepts only direct loops. Other NO proof
families are rejected, even if bare CeTA accepts them. The existing loop checker
also rejects variable left sides. Those are proof-language coverage limits,
not changes to the canonical semantics or completeness claims.

## Parsing, dispatch and remaining trust

Ferrum's `cert check-outermost` binds the original ARI rules, declared signature,
category and answer to an exact CPF Outermost obligation. Weak rules, strategy
flags, normal-form flags, malformed fields and unknown declarations are rejected.
NO additionally checks the finite witness premises above. The independent replay
audit checks original rules and strategy; a separate witness audit checks all
loop symbols and context arities. Quoted symbol names are normalized consistently.

Plain ARI `(format TRS)` does not declare a strategy. The requested category is
explicit; replay passes `--rewrite-strategy outermost`. Recognized source-path
metadata is checked for disagreement. Legacy general parsing can still infer a
strategy from a recognized path; the bound command does not use path inference
as a replacement for the requested category. Unsupported `(strategy ...)` forms
are rejected rather than silently ignored.

Native ARI/XML parsing, comparison and witness validation are not verified in
Isabelle. Their agreement with the semantic parser premises remains trusted,
along with executable provenance, code generation, compiler/runtime, operating
system and Isabelle/HOL foundations. The theorem audit reports the inherited `Regexp_Method.check_eqv` and
`Types_To_Sets.cancel_type_definition` mechanisms; no new oracle or axiom is
introduced. Human approval of
the specification is not recorded by this implementation review.

## Verification and retention

Build with `make isabelle-outermost-integrated`: the lightweight specification,
`Category_Outermost_Bridge` and `Category_Outermost_Integrated` are separate
sessions with admissions disabled. [Evidence receipt](data/outermost-review-20261108.json).

Fresh protected replay retains **207/207 roots: 27 YES and 180 NO**. Every source
binding, repeated unified-checker call and guidance authorization passes.
All 279 category inputs pass preflight; 25 binding cases, 28 Rust Outermost
tests, 37 existing Python audit/harness tests and three independent witness-audit
tests pass. All 180 replayed loops pass the independent signature audit.

The first replay exposed quoted-name comparison errors and one loop using an
invented constant in a constant-free signature. The binder now compares quoted
names consistently; Outermost loop search uses a fresh variable seed when no
constant exists, with existing symbolic validation and concrete CeTA checking.
No source signature is enlarged. Historical failed replay evidence is preserved.

CeTA's executable, generated logic, certificate format and oracle are unchanged.
This is focused Outermost retention, not a combined full-frontier replay,
production promotion or independent two-checker release gate.
