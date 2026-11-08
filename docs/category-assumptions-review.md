---
type: Formal Specification
title: "Category bridge assumptions: review register"
status: draft
---
# Category bridge assumptions: review register

Recorded on 2026-11-08. This register distinguishes compiled conditional theorems
from coverage of every input in the intended category. A hypothesis must follow
from category validity, be proved for the concrete checker configuration, or be
checked on the actual input. Documentation alone does not discharge it.
Human review is pending; no entry below records user approval.

## Review order and current coverage

| Order | Category | Compiled connection | Assumptions and open coverage |
| --- | --- | --- | --- |
| 1 | [TRS Standard](trs-standard-specification.md) | Equivalence; YES and NO | Finite signature-correct rules, infinite variables; correct checker modules and exact Standard configuration. First review below. |
| 2 | [TRS Innermost](trs-innermost-specification.md) | Equivalence; YES and NO | Same problem validity; unrestricted equivalence uses countable symbols and variables. Checker variables are strings. Concrete strict review completed below. |
| 3 | [TRS Relative](trs-relative-specification.md) | Ranked equivalence; YES; conditional NO | Unrestricted equivalence and NO additionally require a symbol of arity at least two in the signature OR no new RHS variables in any weak rule. Full coverage without that condition is unresolved. Concrete guarded review below. |
| 4 | [TRS Context-sensitive](trs-context-sensitive-trust-boundary.md) | Concrete and serialized bound YES/NO | No unchecked module contracts. NO covers containing signatures. YES covers the rule signature or the direct CSR proof language on larger declared signatures; the bound interface checks this guard. Full signature extension for other proof families remains open. |
| 5 | [SRS Standard](srs-specifications.md) | Equivalence; YES and NO through unary encoding | Concrete and serialized YES/NO compiled; per-rule shared-tail encoding and strict original-input binding checked. No extra signature or proof-family guard. See [review](srs-standard-trust-boundary.md). |
| 6 | [SRS Relative](srs-specifications.md) | Equivalence; YES and NO through unary encoding | Concrete and serialized YES/NO compiled; shared-tail encoding in both partitions supplies variable preservation. No extra signature or proof-family guard. See [review](srs-relative-trust-boundary.md). |
| 7 | [SRS Cycle](srs-specifications.md) | Equivalence; three NO checks | Acceptance of transport, embedding or morphism check on the same finite rule list. No YES bridge implemented. Review pending. |
| 8 | Higher-order rewriting | Specification compiles; bridge unfinished | Typed semantics and translations still require review and completed correspondence proofs. |
| 9 | TRS Outermost | Not implemented | Category semantics and bridge obligations pending. |
| 10 | TRS Conditional | Not implemented | Category semantics and bridge obligations pending. |
| 11 | TRS Equational | Not implemented | Category semantics and bridge obligations pending. |

The compiled inventory is in [Spec/ROOT](../thys/Category_Specifications/Spec/ROOT)
and [Bridge/ROOT](../thys/Category_Specifications/Bridge/ROOT).
The integrated build including Context-sensitive passed: specifications 2 seconds,
bridges 39 seconds, total 56 seconds. Its local log is
`target/trs-innermost/package-csr-1.log`; this is a build observation, not a
new immutable source-hash receipt. Earlier receipts remain on the
[package page](category-specifications.md).

## Shared checker obligations

Framework-based corollaries require the appropriate module contracts (`tp_spec`,
`dpp_spec`, and also `ac_tp_spec`/`ac_dpp_spec` for the Context-sensitive dispatcher).
They require exact agreement of rules and strategy configuration and acceptance
with certificate assumptions disabled (`False`). The Cycle Boolean checks have
no certificate-assumption mechanism. Acceptance is the premise of soundness,
not a claim that every true answer has an accepted certificate.

These bridges concern semantic checker inputs. Concrete module instantiation,
parsing, dispatch, generated code and executable identity are separate obligations;
this package has not newly discharged them end to end. No production checker
change is implied by this register.

## 1. TRS Standard: first review

### Mathematical domain

The [shared definition](../thys/Category_Specifications/Spec/TRS_Spec_Base.thy)
uses finite first-order trees, an infinite variable supply and a partial function
assigning each permitted symbol exactly one arity. Rules form a finite set and
both sides respect that signature. The signature itself need not be finite or
contain a constant. Terms and substitution images may contain variables.
Rewriting can take place in any one-hole context at any depth.

The input-validity predicate does not exclude variable left sides or extra
right-side variables. This deliberately follows the original specification
request. If the external category excludes these rules, its admissible inputs
are a subset; this broader definition does not itself show that the parser
recognizes exactly that subset. The intended external input conventions still
need human review.

### Semantic hypotheses

`trs_standard_terminates_iff_signature` proves correspondence to signature-restricted
ordinary rewriting without extra hypotheses. `trs_standard_terminates_iff` and
`trs_standard_nonterminates_iff` assume only `standard_problem A R`: infinite
variables, finite rules and signature-correct rule sides. The proof invokes the
existing signature-extension theorem; it does not assume the equivalence it is
meant to establish. There is no additional groundness, constant-symbol,
nonvariable-left-side or RHS-variable-preservation requirement.

Consequently the current Standard bridge has no outstanding extra semantic
restriction analogous to Relative's NO condition. This conclusion is about
the stated ranked domain, not a completed audit of an external category format.

### Checker hypotheses

Both `trs_standard_checker_YES` and `trs_standard_checker_NO` require:

- `standard_problem A R` and correct operation modules `tp_spec I`, `dpp_spec J`;
- `nfs = False`, empty `Q`, and no weak rules;
- the strict checker rules equal the translated specification rules;
- acceptance by the corresponding termination/nontermination checker with
  certificate assumptions disabled.

The checker API uses string variables and labelled symbols, with its required
symbol interfaces. These hypotheses connect the intended problem to the actual
call. The bridge remains parameterized by the modules; it does not newly prove
that production dispatch supplies those modules and fields for every input.

### Review disposition

Source inspection supports both semantic directions and both conditional
checker-soundness conclusions for the stated domain. Normal Isabelle builds
and inherited-admission checks passed, as recorded on the Standard page.
Human review should first settle whether the ranked domain and admissible-rule
conventions above are the intended Standard category. Concrete module and
input-path instantiation remain separate work. No human approval is recorded.

## Standard review update: TPDB and input path

The [TPDB and input-path review](trs-standard-input-review.md) confirms that
TermCOMP explicitly allows arbitrary term pairs: the variable-rule convention
is resolved against the published category definition. Existing integrated
soundness also discharges the concrete module contracts for parsed inputs.
Original-benchmark binding, frontend validation and composing the integrated
theorem with the canonical specification remain open; this is not an
end-to-end completion claim. The initial review above records the earlier
state of the review and is qualified by these findings.

## Standard completion work: concrete checker and original input

The [integrated checking and trust-boundary page](trs-standard-trust-boundary.md)
tracks the concrete checker composition, serialized parser premise, and new
original-input gates. The integrated build passed on 2026-11-08, including the serialized entry point
and admission audit. Runtime original-input gates and their mutation tests also
passed. The remaining parser, execution and deployment trust boundary is
explicit on that page. The Innermost completion below supersedes its previous
output-mode mismatch.

## 2. TRS Innermost: strict review completed

The [Innermost trust-boundary review](trs-innermost-trust-boundary.md) records
concrete integrated and serialized YES/NO soundness, with explicit `nfs=false`
and certificate assumptions disabled. Concrete module obligations are proved;
there is no additional rule-shape requirement. Countability is satisfied by the
actual representation. Rust and independent replay gates enforce exact original
rules, category, strategy and decision. True and omitted root flags are rejected.
Unverified parsing/comparison, executable provenance, runtime and inherited
Isabelle oracles remain trusted, as for Standard. No human approval, production
promotion, full replay, or checker completeness is claimed.

## 3. TRS Relative: ranked signature review

The [concrete review](trs-relative-trust-boundary.md) confirms that the extension
condition cannot simply be removed: the library proves a counterexample, also
reproduced against direct CeTA. YES has no extra restriction. The bound NO path
checks a declared branching symbol or the weak-rule variable condition and
rejects unsupported cases. Concrete module contracts are discharged, both
partitions are bound to the original input, and certificate assumptions are
disabled. Full ranked NO coverage remains open; the guarded interface does not
claim an unconditional unrestricted equivalence. Parsing/comparison, execution,
artifact provenance and inherited Isabelle mechanisms remain trusted.

## 4. TRS Context-sensitive: declared-signature review

The [concrete review](trs-context-sensitive-trust-boundary.md) preserves the
canonical ranked specification and discharges the concrete checker modules.
ARI declarations and all replacement maps, including unused symbols, are now
validated and bound to the CPF. NO transfers to the complete declared signature.
The direct CSR proof language has an instantiated unrestricted YES theorem;
other YES proof families require a checked equality with the rule signature.
There is no unchecked signature-extension assumption. That checked restriction
is still a coverage limit and does not establish a general extension theorem.
Normal builds and admission/oracle audits pass. The inherited trust mechanisms
and parser/execution boundary are recorded explicitly. No human approval is
recorded by this implementation update.

## 5. SRS Standard: concrete review completed

The [review](srs-standard-trust-boundary.md) connects arbitrary per-rule tail
variables to the word semantics and discharges the concrete module contracts.
The bound interface checks the published unary category and exact unrestricted
CPF obligation, with certificate assumptions disabled. Both answers have no
extra semantic coverage guard. All 1,720 protected SRS roots and all 3,610
five-category roots pass fresh strict replay and independent audits. The
parser/execution and inherited-oracle trust boundary remains explicit.

## 6. SRS Relative: concrete review completed

The [review](srs-relative-trust-boundary.md) proves correspondence for both rule
partitions with independently named shared tails and instantiates the concrete
checker with certificate assumptions disabled. Weak-only loops remain allowed.
Both answers need no extra semantic coverage guard. Strict original-input
binding, 403-root focused replay and 4,013-root six-category replay pass.
The parser/execution and inherited-oracle trust boundary remains explicit.
