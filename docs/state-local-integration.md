---
type: Implementation Plan
title: "State-local checker integration"
status: draft
---
# State-local checker integration

The authoritative [Ferrum architecture contract](../../ferrum/docs/architecture.md) governs this implementation. Follow its [processor](../../ferrum/docs/processor-contract.md), [identity](../../ferrum/docs/state-identity.md), [guidance](../../ferrum/docs/guidance-contract.md), and [release](../../ferrum/docs/release-gates.md) contracts.

The snapshot starts at CeTA main 6ce5ab3. Historical unified ITS validation is retained under `unified-its-20261027/`. No checker logic changed in this milestone. Preserve the independently built unified executable and verified libraries; fix stale callers rather than substituting category executables. Regenerate affected exports from Isabelle. Release evidence must bind every category to one immutable executable hash.

The full architecture release has not passed: independent CeTA-Lean ITS coverage and the new 15-category two-checker replay remain open. Cross-repository links target the maintained sibling Ferrum checkout; release evidence must pin the repository revisions. CeTA checking logic and the installed executable remain unchanged.

## Existing triple checkers connected to the unified adapter

Revision `3344eae` connects the already exported initial and return-family triple
checking functions to the LP adapter. No generated module, Isabelle theorem or
export archive changed; all other category libraries retain their hashes.
The isolated O2 binary is
`b4165eefc964f4417cb184cc4545f7437dbcfd2acacca15f2f7ed122c6406a52`.
The installed main executable is unchanged. The candidate passes 49 retained
LP/cut positive certificates and 49 negatives, plus dispatch rejection tests.
Ferrum `7a7fc41` separately passes six fresh initial-triple proof runs with two
checks each and six semantic mutations. Return-triple families still require
fresh per-family migration gates. The full-frontier gate remains open.
[Recorded regression checks](data/lp-triples-dispatch-3344eae-validation.json)
and the private build at `target/unified-lp-triples` retain the evidence.

## Finite LP artifact dispatch

Revision `54a99ee` adds the existing Isabelle-generated finite-LP checker to the
same LP library and unified dispatcher. The imported export is byte-identical
to the verified `lp-finite-production-v2-20261021` snapshot; its four recorded
LP theory files are byte-identical to the current checkout. The preserved
[export identity](data/lp-finite-export-20261021-identity.json) records its source
revision and parent environment. No existing generated module was edited, and
other category libraries retain their archive hashes.

The isolated O2 executable at `target/unified-lp-finite/ceta` has SHA-256
`c89d366b2d2c57d73f8fe13157975882814a0af1cff2ebba6584bfbfdb9e0f44`.
It passes 346 positive checks and 81 negative checks, including all 91 retained
cut roots, plus the finite-artifact and unified-dispatch regression tests.
[Validation evidence](data/lp-finite-unified-54a99ee-validation.json).
The previous `b4165eef...` candidate and main executable are preserved. This
is a checker-library regression gate, not a new full-frontier replay.

## CSR rule-removal / GM composition candidate

The current candidate adds signature-preserving rule-removal soundness lemmas
in `CSR_Signature_Rule_Removal.thy` and composes arbitrary polynomial/matrix
removal prefixes with GM in `CSR_GM_Transformation.thy`. GM's conclusion is
signature-restricted; the composition preserves the caller's signature rather
than assuming unrestricted termination of the residual. The parser accepts an
optional sequence of `ruleRemoval` children inside `csrGmTransformation`;
existing artifacts use an empty sequence.

The complete production Isabelle build and export passed with proof checking
enabled. The new unified O2 checker has SHA-256
`c3e853ea0a13cd5543797f6d6e5e0ece8046b9102a708a42cb607ee1f539da49`.
It passes eight positive checks over four composition fixtures and rejects all
20 semantic mutations. All 110 retained CSR certificates pass two checks each.
The reproducible fixture gate is `tests/unified/check_csr_gm_composition.py`.

[Export identities and certificate evidence](data/csr-gm-composition-20261029-validation.json)
record the source snapshot, generated-module hashes and checking results.
Only the CPF generated module changed; other category exports remain unchanged.
No generated checking logic was edited. The old export archive and production
executable are preserved. Fresh native/strict replay and the full-frontier gate
remain pending. See Ferrum's
[composition contract](../../ferrum-state-local/docs/csr-proof-composition.md)
for state identity and runtime integration gates.


The Prolog helper-return extension adds `prologContextComposedDependencyTriplesProof`
to the existing unified LP adapter. Its prefix and continuation use the shared
answer-sensitive return graph, with checked scope separation, saved answers,
failure branches and stack-destroying errors. The root theorem requires a checked
common PiDP residual; a helper termination proof alone cannot establish its
returned-value relation. The constructor does not import ordinary-cut groundness
summaries into Prolog.

The regenerated `Prolog_Context_Generated` export retains the existing contextual
entry point and adds the composed entry point. The hash-verified snapshot is
`tests/unified/exports/lp-context-composed.tar.gz`. Isabelle verification and the
dependency audit pass in `target/prolog-composed-verify-297.log`; the original
export is retained in `target/prolog-composed-export-270`. Unified build and
category-library receipts are in `target/prolog-composed-unified-272`. Ferrum's
`target/prolog-composed-baseline-289` strictly preserves 17 YES and three NOs on
all 221 Prolog inputs using that same checker. This development integration does
not establish the protected-category production release gate.

The established-SEG extension is integrated at CeTA
`3b49a96dd2c2ec992f1468bea33832dded4b72d9` on `codex/prolog-source`.
`prologEstablishedSEGDependencyTriplesProof` checks the existing graph's finite
referenced modules, complete local control, saved contexts and exact common
triples child. Actual successful return properties remain separate obligations
from helper termination. The generated export is
`tests/unified/exports/lp-established-returns.tar.gz`; Isabelle verification and
export evidence is retained in `target/prolog-free-staged-export-49.log`.

The unified `make ceta` build `target/prolog-free-staged-unified-54/ceta` has
SHA-256 `4c050baa2cfba9cc74ca3bc4d1ab8199a263ef2c776d0cd4829169f6be1292a3`.
With Ferrum `1a8f8e348ce9f9b18c21f1d9ca02253fcb8c4d99`, fresh strict replay
certifies 18 Prolog YESs and three NOs on all 221 inputs, and preserves 84
LP-with-cut YESs and nine NOs on all 112 inputs. Each retained source result is
audited and checked twice with that executable. The 30-gain milestone and
protected-category promotion gate remain open. Additional source return-model
theories under development are not exported by this snapshot.

## Established source integer returns, 2026-10-30

Commit `8dd70dba936a951a5e7aad2cb111ecbfc9c2ec2c` adds a checked model of
actual successful source returns and instantiates it for integer facts across
established SEG Splits. It covers every reachable clause and applicable builtin,
uses the shared conditional transfer checker, and keeps return properties
separate from termination. The shared LP-with-cut operational semantics supplies
all execution, substitution, saved-alternative and answer transitions.

Verification and dependency audits pass in
`target/prolog-source-integer-wire-92.log` and the verified export log
`target/prolog-source-integer-wire-export-93.log`. The exported archive is
`tests/unified/exports/lp-source-integer-returns-wire.tar.gz`. The unified
`make ceta` build at `target/prolog-source-integer-unified-94/ceta` has SHA-256
`2c3688af4b0560a6ec71efbe1c782f3a19f3f32febb9addcc60f7e0b76950080`.
No generated checking logic was edited.

Ferrum integration `a30a21cad9e47e1ac0ad7c10a8d715a7e8097293` strictly replays
20 YESs and three NOs on the fixed 221 Prolog roots, preserving every previous
verdict. The same checker preserves 84 YESs and nine NOs on all 112 LP-with-cut
roots. All retained results have original-source audits, complete receipts and
two checks. Three mutation suites pass 29 checks each; nine strict advice
controls pass. Evidence is pinned in Ferrum's
`docs/data/prolog-source-returns-frontier-20261030.json` and accompanying archive.
The requested 30-gain milestone has achieved three gains and remains active;
protected-category promotion is still gated.

## Established finite-ground returns, 2026-10-30

Commit `df37ebf0b913f2f5803d19a51a41ef0b4bc72157` checks actual successful
finite-ground returns across nested established SEG Splits and all three finite
comparison outcomes. It preserves shared operational semantics and separates
return properties from termination. Checked source contexts transport groundness
without treating ground values as integers. Generated checking logic is unchanged
by hand; `tests/unified/exports/lp-source-ground-returns.tar.gz` comes from the
verified export in `target/prolog-ground-export-133`.

The unified `make ceta` build at `target/prolog-ground-unified-135/ceta` has
SHA-256 `692c9aa4f713aff1a0e1697b06364a0eadae11373ec701b94b986c8b4c292376`.
Ferrum `50ebaceae51b5dfdcf68a22f7026334603b906e2` strictly certifies 30 YESs
and three NOs on all 221 Prolog roots and preserves 84 YESs and nine NOs on all
112 LP-with-cut roots with this checker. Every retained result is source-audited,
checked twice and reconstructed from authorized witness-free guidance.
[Persistent audit evidence](../../ferrum-prolog-shared/docs/data/prolog-ground-returns-frontier-20261030.json)
records the full validation and remaining obligations. The requested 30-gain
milestone still needs 17 additional YES roots. Protected-category promotion is
not claimed. Arithmetic normalization theories under development are not part
of this pinned checker.

## Established identity interfaces and normalized evaluation, 2026-10-30

CeTA `c37fd837d569716a9712fa5802b716145992fb1f` verifies identity tests and constant/integer evaluation
normalization with complete referenced-module dependencies. Successful identity
links may use either independently checked specialized or original interfaces.
Export `tests/unified/exports/lp-source-normalized-identity-interfaces.tar.gz`
comes from verified `target/prolog-identity-export-180`; unified `make ceta`
build `target/prolog-identity-unified-182/ceta` has SHA-256
`995b2317fb0d269aefc517a3a5097889e53999b20a8e0ba6a7f8b662a99b5de0`. No generated checking logic was edited manually.

Ferrum `022386693f7ff7e10cc0c6f19e9289cf50615735` strictly replays all 221 Prolog roots to 31 YES
and three NOs, preserving previous verdicts with source audits, authorized
receipts and two checks each. The same checker preserves 84 YES and nine NOs
on all 112 LP-with-cut roots. The cohort has 32 cases, strict controls 63 cases,
and mutation validation 705 checks; redundant annotation removals are explicitly
classified, with necessary removals rejecting in the cohort. Immutable audit
metadata and archived evidence are in the sibling Ferrum ledger at
`docs/data/prolog-identity-normalization-frontier-20261030.json`.

Fourteen of the required 30 additional YESs are certified. Equality free-knowledge
transport and finite-ground arithmetic remain active development. Production
promotion remains gated on protected-category replay with the same checker.

## Equality preserves untouched free variables, 2026-10-30

`f48a500cf730b687f9b858b3404f49353347d41e` adds a checked MGU continuation theorem and uses it in
the established source equality receipt. It requires ground/free coverage of
both operands, distinct incoming free variables, untouchedness, continuation
occurrence and refresh bounds. The established graph is unchanged.

Verification 202, export 204 and unified `make ceta` build 206 pass. Checker
SHA-256 is `dd33df0536f6ac474f004befd18d1ac223b3d3567dff20934b5d39d3e141a081`. Fresh strict replay preserves 31 Prolog
YESs and three NOs on 221 roots, and 84 cut YESs and nine NOs on 112 roots,
with two checks each and authorized receipts. All 33 cohort cases, 739 mutation
checks and 66 strict controls pass. Pinned evidence is in the sibling Ferrum
`docs/data/prolog-free-equality-preservation-20261030.json` and archive.

There is no additional benchmark gain in this checker-only integration. Finite
evaluation foundations at `877bdc0` and subsequent contextual transport proofs
remain separate development; they are not exported in this checker. The milestone
still requires 16 more YES roots, and protected-category promotion remains gated.

## Established finite evaluation milestone, 2026-10-30

Source commit `5f4e343f43d7cce1997a594705ff01eb4a5f2d5b` checks finite-ground arithmetic and conditional actual
helper returns within the established Prolog SEG. It reuses the shared
LP-with-cut answer semantics, retains failure/error alternatives and complete
nested module dependencies, and keeps groundness separate from integer facts.
The new XML constructor is `prologEstablishedFiniteSEGDependencyTriplesProof`;
legacy constructors remain supported by the same unified executable.

Isabelle verification 246 and export 247 pass. Unified `make ceta` build 249
has SHA-256 `88d8e3f093ac8d9e14b82b67ec8e212640053075cbb1f710bf2564f6ea20f220`. Export commit `5fba3d458c5385a1dae150c148442fd6c201599d` pins
`tests/unified/exports/lp-source-finite-observed-evaluation.tar.gz`; generated
checking logic was not edited manually. The persistent tree is
`/work/dfm/festschrift/CeTA-prolog-source`, branch `codex/prolog-source`.

Ferrum `3181c5cbda4e6278163bb917a30e4c504235b84e` strictly replays all 221 roots to **48 YES + 3 NO**,
31 additional YESs over the milestone baseline, and preserves **84 YES +
nine NO** on all 112 cut roots with this same checker. Every retained result
has original-source audits, two checks and authorized complete receipts.
Validation includes 467 shared tests, 43 final cohort cases, 33 legacy cases,
five further negative controls, 701 mutation-suite checks and 66 strict replay
controls. [Pinned audit metadata](../../ferrum-prolog-shared/docs/data/prolog-finite-milestone-20261030.json)
and its archive retain exact identities and all attempts. The requested
30-gain development milestone is complete; protected-category production
promotion and a fresh matched AProVE comparison remain separate gates.


## Prolog sharing equations (source integration in progress)

`LP_Ground_Equations` proves bounded finite-groundness propagation through
actual term equations and preservation under runtime substitution. Equation
observations reuse the existing source contexts and saved-frame transport.
They are not integer evidence. The checked context can initialize an equation
only from an existing equation or reflexive instantiated terms.

Verification logs `target/prolog-ground-equations-126.log`,
`target/prolog-equation-context-128.log` and
`target/prolog-equation-ground-130.log` pass, including shared-field groundness,
missing-equation rejection, cyclic-equation rejection and initialization controls.
Failed attempts 125, 127 and 129 remain preserved; 127 exposed the required
explicit rejection of equations in the numeric-guard checker. Full source
pipeline 131 and six-function export 132 pass their dependency audits. Ferrum
`96f01a2` implements bounded equation-interface discovery over the established
graph, with every incoming edge retained for independent context checking.
Its 491 shared tests pass, including a shared-field source-assembly regression.
The unified `make ceta` build 134 passed from the verified export, with unchanged
non-LP libraries. Its SHA-256 is
`c7972d18a9a092a5312286a76849784d34e4acef76db0300cbfaaa878165c7eb`.
[Export and build identities](data/prolog-equation-export-20261031.json) retain
the proof and archive hashes. Ferrum source certification and full-frontier
validation are being recorded separately. No generated
checker code was edited and no benchmark gain is claimed from these components.


## Prolog finite-length return foundation

`LP_Prolog_Finite_Length` proves uniqueness and substitution stability of a
finite observed list-spine count, rejects a cyclic spine, and proves that a
successful scalar unification returns its actual nonnegative integer count.
List elements remain arbitrary infinitary terms. The error outcome remains
explicit; this relation does not certify termination of an open-list generator.
The theory is registered in `Prolog_Arithmetic_Bridge`.

Isabelle attempt 140 verifies all lemmas and the dependency audit from the
verified equation-export heap 132. Attempts 135–139 retain interrupted proof
search and rejected proof steps. [Metadata](data/prolog-finite-length-20261031.json)
and [source/log archive](data/prolog-finite-length-20261031.tar.gz) pin the result.
No generated code, unified executable or accepted source-proof constructor has
changed. Source-action coverage and actual-return model integration remain
required before benchmark certificates or gains can be claimed.


## Checked finite length and helper return integration

Source commits `a5adef5` and `8f45239` add finite-input length normalization,
explicit failure/error outcomes, fresh result checking and conditional integer
return facts. Groundness may come from the checked incoming context. Existing
empty return summaries remain replayable. Full Isabelle exports 148 and 151
pass; generated checking logic was not edited.

[Integration metadata](data/prolog-length-integration-20261031.json) and
[attempt logs](data/prolog-length-integration-20261031.tar.gz) pin unified checker
153. Ferrum strict replay 328 preserves 54 YES + 3 NO; cut replay 331 checks all
84 YES + 9 NO certificates twice with that same checker. Three length fixtures
certify, nine strict controls and fifty mutations pass. No benchmark gain is
claimed. Non-LP library identities and dispatcher source match checker 134;
this comparison is not a protected-category production replay or promotion.

The established library expansion through `length_count` remains an explicit
source-assembly obligation. Direct scalar normalization does not replace that
graph, omit its helper dependencies or certify an open-list generator.


Shared library-expansion contract attempt 154 verifies reachability inheritance
and silent initial expansion in `LP_Answer_Initial_Refinement`. The rule requires
the complete expanded-state contract and coverage of every primitive successor
in the same annotated transition system. Return facts alone cannot discharge
these premises. [Metadata](data/prolog-library-expansion-contract-20261031.json)
and [proof audit](data/prolog-library-expansion-contract-20261031.tar.gz) retain
the successful check with no skipped proofs or oracle dependencies. Concrete
`length_count` coverage, including saved alternatives, is still unproved; the
installed checker and certified frontier are unchanged.

## Prolog finite comparison errors (2026-10-31)

Source commit `4e5ab1e` checks uncaught comparison errors when a root operand
is proved free and the other operand is finite ground or proved free. Query
mode `f` alone supplies no such fact. The source transition terminates the
entire stack, including saved alternatives; cyclic other operands remain
unsupported. Successful comparison observations retain their existing rules.

[Verification evidence](data/prolog-free-comparison-integration-20261031.json)
pins verified export 161 and unified checker 163. Strict Prolog replay preserves
54 YES + 3 NO, and all 84 YES + 9 NO retained cut certificates pass twice.
There are no new benchmark gains. Non-LP library identities and the unified
main are unchanged from checker 153; this comparison is not a protected-category
production replay. Failed intermediate proof attempts remain in the audit archive.

## General rational disequality: one benchmark recovery (2026-10-31)

Source `f7af9f2` extends the same interpreted builtin relation to rational
disequality. Success means absence of a rational unifier and performs no
substitution; its non-unifiability guard is carried only on the success
continuation. The existing finite-ground constructor remains replayable.
The new `rationalDisequality` constructor checks both outcomes and every link.

[Verified integration](data/prolog-rational-disequality-integration-20261031.json)
pins full export 171 and unified checker 173. Ferrum `5cc245d` recovers
`AProVE_10_prolog/nounify.pl`, including strict replay: **55 YES + 3 NO / 221**.
All 58 source receipts are authorized; 24 mutations and 15 strict controls pass.
All 84 YES + 9 NO retained cut certificates pass twice with the same executable.
Non-LP library identities and the unified main are unchanged from checker 163;
protected-category production replay remains pending. Earlier rejected proof
attempts are retained in the archive, without proof admissions.

## Literal probes and checked helper returns (2026-11-04)

Source `5a928df` adds literal `once` and negation probe steps to the existing
Prolog semantics and checks their fresh scopes, saved alternatives and bindings.
The finite triples return contract now receives the node's established knowledge:
a checked contradictory guard can exclude an impossible successful return.
Ordinary structural emission receipts remain accepted. Referenced helper modules
and their termination obligations remain present.

Verified export 229 and unified build 231 yield checker
`9d40ec078008931560ded8ab06176a822613eac3ed3a22fcd569dd28e96b1b0d`.
Ferrum source `8c9ba3c` strictly replays **56 YES + 3 NO / 221**, including the
new `addneg.pl` result, with all 59 receipts authorized. All 84 YES + 9 NO
retained LP-with-cut certificates pass twice with the same executable;
40 mutations and 24 strict controls pass. The non-LP libraries and unified
main retain their identities. Protected-category production replay is pending.
[Integration evidence](../../ferrum-prolog-release/docs/data/prolog-reachable-returns-integration-20261104.json)
includes the proof attempts, source hashes, generated export identity,
checker build, failed initial replay and successful fresh guidance migration.

## Finite instantiation errors (2026-11-04)

Source `c3d204a` proves finite arithmetic instantiation errors using a genuinely
free expression variable and finite other operands. It extends the existing
source-control contract to prove that the uncaught error discards the entire
stack. Unknown and cyclic other operands do not satisfy the new check.
Verified export 242 and unified build 244 yield checker
`8f3896730bc920d8534bdf9d79ffca64fdfe8bb6719ff82548d4da368a0d850c`.

Ferrum source `28b109f` strictly replays **57 YES + 3 NO / 221**, with all
60 complete receipts authorized and two checks per retained verdict.
The same checker accepts all 93 retained LP-with-cut certificates twice
(84 YES and 9 NO). Validation includes 65 mutations, 33 strict controls,
and 499 shared tests with five ignored. A positive finite-error example with
a divergent later alternative remains UNKNOWN: eliminating the unreachable
alternative still needs checked assembly evidence.

[Complete integration evidence](../../ferrum-prolog-release/docs/data/prolog-finite-instantiation-integration-20261104.json)
pins source identities, proof attempts, export and build identities, the full
strict replay, and witness-free guidance. Protected-category production replay
and matched AProVE comparison remain open; this is not production promotion.

## Rational graph equation bridge under development (2026-11-04)

`LP_Rational_Graph_Equations` describes cyclic runtime values using the existing
infinitary terms. It proves a graph denotation, uniqueness under checked
reference bounds, substitution transport, and equivalence between the graph
model and finite equation receipts. A one-node self-cycle is proved not to be
finite ground; a dangling reference fails validity. The final dependency audit
rejects every oracle and skipped proof.

Fresh theory verification from heap 242 passes in
`target/prolog-rational-graph-equations-251.log`; attempts 245 through 250 remain
available, including failed proof attempts. The source-envelope connection and
unified export remain open. These theorems do not add a certified Prolog root
or change the released checker identity.

## Initialized rational equations: unreleased integration

Full XML verification 260 (`target/prolog-equation-congruence-control-260.log`)
passes for successful-unification equation initialization and constructor
congruence in the equation-rewrite action (commit `1a5b656`). Verification 261
proves the independent `LP_Equation_Congruence` checker and its soundness lemma
(commit `066f60c`). Neither is included in released unified checker 244.

The follow-up context-observation transport change is still under verification.
Attempt 266 exposed incompatible older builtin definitions in its dependency
heap; attempt 267 lacked the named arithmetic-session preload. Both failures
are retained. Attempt 268 rebuilds the affected theories from the newer heap,
with stale context and finite-evaluation theories explicitly removed before
preloading and finishing dependencies. Full XML and equation regression check
269 is conditional on successful completion of 268. These pending checks do
not establish a source certificate or a new benchmark verdict.

Ferrum `52a3a06` passes 504 shared tests (five ignored); complete strict replay
525 preserves 57 YES and three NO with unchanged unified checker 244, and all
60 receipts are authorized. The two targeted rational roots remain UNKNOWN
at graph-wrapped callable source assembly. [Pinned preservation evidence](../../ferrum-prolog-release/docs/data/prolog-rational-transport-preservation-20261104.json)
separates that result from the unreleased checker work.

Verification 268 has now passed for equation congruence in context observation
transport. Full XML integration 269 also passes, including the rotated-cycle
positive case, missing-initialization rejection and cyclic-groundness negative
control. Commit `615eb6d` contains the tested context change and refactoring;
[immutable verification records](data/prolog-equation-transport-20261104.json)
pin the source manifest, successful logs and failed rebuild attempts 266/267.
The unified executable has not been regenerated from this work. Complete
rational source assembly and benchmark gains remain open.

### Selected-clause equation observations (2026-11-04)

Source `355fa92` on `codex/prolog-production-integration` adds
`LPPEClauseEquationRewrite` beside the existing goal-frame rewrite. An
initialized equation can expose constructors in a selected clause's call;
the clause index, cut scope, continuation, saved alternatives and return rows
stay identical. The existing checked link must provide a strict residual edge.
The full evaluation control theorem and XML parser verify in run 270.
[Pinned source identity and verification](data/prolog-clause-equation-rewrite-20261104.json)
record the unreleased change under `thys/Logic_Programming/` in the persistent
`CeTA-prolog-release` tree. No generated checking logic was edited, no new
checker was released, and no benchmark gain or production promotion is claimed.

## Certified rational source observations, 2026-11-04

Commit `61b8fb7` integrates the verified rational equation initialization,
congruence and selected-clause rewrite rules into the six-function Prolog
context export. Source proof commit `355fa92` and export run 272 pass the
Isabelle theorem/dependency audit. No generated checker logic was edited.
[Pinned export, source and build evidence](data/prolog-rational-equation-export-20261104.json)
records `make ceta` unified build 274, hash
`e603074c5b87bc9415162bd744ace909af48bd9397f4478fe03a80f57c553fc5`.
The diagnostic category option always exits unsuccessfully and cannot authorize
a verdict, even when every diagnostic item is true.

Ferrum `3a1ea6c` strictly replays all 221 Prolog roots at **59 YES + 3 NO**,
including two new rational source gains. Every retained result receives source
audits, two checks with this executable and receipt authorization. The same
executable accepts all 93 retained LP-with-cut certificates in 186 checks.
Fourteen semantic mutations of the new source proofs are rejected; renamed
positives and divergent/cyclic negative controls pass. The [Ferrum evidence](../../ferrum-prolog-release/docs/data/prolog-rational-gains-20261104.json)
retains the complete attempts and guidance controls. Protected-category
production promotion and the broader superiority comparison remain open.

## 2026-11-04 Constructor transport for dependency-triple returns

Source commit `c7c382b` proves data erasure for actual SEG answer steps, finite
successful prefixes and dependency-triple calls. The constructor-success
machine theorem additionally transports the saved continuation bindings with
the actual helper return. It reuses the existing LP operational semantics and
constructor rewrite relation, retaining infinite constructor values. It does
not infer finite spines or termination from a successful return.

[Verified sources and attempts](data/prolog-triple-constructor-success-20261104.json)
include the initial proof failure, final checked theories, proof-oracle audit
and immutable child-heap identity. The theories are registered in the standard
Logic_Programming session. This is a prerequisite for the constructor-triples
source bridge, not an accepting checker extension. Strict-call simulation,
constructor-chain assembly and source checking remain open. No Haskell export
or unified checker changed; retained executable 274 is still authoritative.


## Rational Prolog source nontermination

Integration `c68ffa9` adds an independently generated rational-NO module to the
unified LP/Prolog adapter. All 18 previous generated modules remain byte-identical.
The original source semantics and previous constructors are unchanged. The new
source theorem checks a principal cyclic binding, exact rational pattern matches,
finite observations proving failed unification, and complete ordered traces with
saved alternatives. It reuses the shared MGU source and pending-stack pumping
theorem; a cyclic graph is not a finite structural measure.

Isabelle verifies the source theorem and executable equations with no skipped
proofs or oracle dependencies. `make ceta` builds the O2 unified executable at
`target/unified-rational-no-349/ceta`, SHA-256
`0e32d5a6cf49a5c86bccbfe6de6dbfca5087595c8f5ca45e65a61b0865e772a8`.
The real `nonterm.pl` and three generalized fixtures pass native and strict
Ferrum replay with two checks each; all 17 mutated certificates reject twice.
[Proof, export and mutation evidence](data/prolog-rational-no-20261104.json)
pins every attempt. Full frontier preservation and production promotion remain
pending: the user requested a break once `nonterm.pl` was proven NO.

## Finite guarded source composition lemmas

Proof revision `d753ac1` adds finite guarded descent for the existing region,
child and nested Split contracts, a context theorem for actual successful
helper returns, and a finite-evaluation simulation into the existing checked
integer ITS component. Isabelle verification and the dependency audit pass in
`target/prolog-guarded-composition-367.log`; the reproducible entry point is
`scripts/verify_prolog_finite_guarded.py`, also included in the
`Prolog_Arithmetic_Bridge` session. [Pinned source identities and verification](data/prolog-finite-guarded-theorems-20261104.json).

These are composition interfaces, not an executable numeric source-proof
constructor. Complete source/module coverage, checked projections and uncovered
non-integer branches remain obligations. The checker export and unified
executable are unchanged. Separately, Ferrum `a07828b` uses the existing checker
for arithmetic-return proof parameters and combined integer/ground Split
receipts, preserving 59 YES + 4 NO Prolog and 84 YES + 9 NO LP-with-cut in fresh
strict replay. It establishes no new benchmark gain or production promotion.
## Sparse tiling: local simulation infrastructure

The isolated `codex/policy-sparse-tiling` worktree starts from checker source
`0a3cca39bf93b0b43b44d89c95d439e93279d603`. Session
`Sparse_Tiling_Construction` now checks the string-step context lemma, closure
of chains inside an invariant language, and transfer of local termination
through a step simulation. The gate passes in `target/sparse-tiling-build-4.log`
with Isabelle2025-2 and AFP snapshot `/work/dfm/afp-2026-07-21`.
The source is `thys/Sparse_Tiling/Sparse_Tiling_Simulation.thy`.

The first attempt was stopped during broad AFP metadata discovery; attempts two
and three contain failed proof obligations, preserved alongside the successful
fourth attempt. The proof contains no admissions. Builds use a private Isabelle
home and persistent temporary directory under this worktree's `target/`.

This is proof infrastructure only. Instantiation for the concrete shift algebra,
RFC coverage, executable certificate checks, parsing, and unified dispatch are
unfinished. No generated checker logic, library export, or CeTA executable has
changed. Ferrum's learned-policy campaigns continue with their pinned checker.

The concrete `Sparse_Tiling_Paths` theory now passes the same isolated session
in `target/sparse-tiling-build-9.log`. It defines shift runs and tile paths and
proves their append laws, preservation of state length, the explicit suffix
formula, synchronization, and contextual simulation of a source rewrite by a
supplied tiled rule. Attempts five through eight retain intermediate proof
failures; the final session checks both theories without admissions.

This proves the path-level simulation component, not the complete sparse-tiling
processor. Language closure from finite checks, RFC coverage, term/source
correspondence, certificate parsing and executable dispatch are still missing.
Generated checking code and the pinned executable remain unchanged.

`Sparse_Tiling_Language` now verifies the accepted-language component. Its
explicit tile condition implies closure under source rewriting and simulation
of each bordered source step; termination of the tiled system then implies
local termination on that accepted language. The gate passes in
`target/sparse-tiling-build-11.log`, with attempt ten's failed obligations
preserved. Nonempty source left sides and equal border/state lengths are
explicit assumptions.

This result still assumes the tile condition rather than proving an executable
finite check for it. Initial/RFC coverage, source-term correspondence and
certificate integration remain unfinished. No checker executable changed.

`Sparse_Tiling_Check` now proves finite path-context enumeration complete and
proves that its list-based closure/residual check implies the tile condition.
The resulting executable predicate transfers termination of the tiled system
to local termination on the accepted source language. Gate:
`target/sparse-tiling-build-20.log`, including SML code-generation compilation,
a positive deletion example, a missing-residual rejection, and an empty-left
rejection. No admissions are used. Attempts 12–19 preserve syntax/proof
failures, interrupted automation diagnostics, and the earlier successful proof
and code-generation checks.

Initial/RFC coverage, source-term correspondence, certificate parsing and
unified dispatch remain unfinished. No generated production export or checker
executable changed. This isolated source is on `codex/policy-sparse-tiling` in
`CeTA-policy-eval`; campaign checker identities remain unchanged.

`Sparse_Tiling_Coverage` now defines the string closure generated by right-hand
sides, source rewriting, and proper nonempty prefix/suffix overlaps. It proves
that the accepted tile language contains this closure. Its executable initial
and suffix checks, combined with the earlier normal-step check and residual
termination, imply local termination on that closure. The gate passes in
`target/sparse-tiling-build-28.log`, including SML compilation and a positive
example plus missing-initial/missing-suffix tile rejections. Attempts 21–27
preserve intermediate proof failures and the earlier successful abstract
coverage proof.

`Sparse_Tiling_Windows` in the same session proves equality between sliding
windows of a bordered word and the shift paths used in the simulation.
The global RFC termination criterion for this string closure and its connection
to CeTA source terms remain unproved here. Certificate parsing and unified
dispatch also remain pending. No production checker executable changed.

`Sparse_Tiling_Termination` closes the global string-level soundness gap. It
proves termination of the rewrite/suffix order restricted to terminating
strings, decomposes rewrites across concatenation, proves termination of an RFC
prefix followed by a terminating suffix, and derives global termination from
termination on the explicit string RFC. Consequently
`sparse_check_termination_sound` proves that the executable coverage check and
termination of its tiled residual imply termination of the entire source
string system. No proof admissions or additional unverified criterion are used.

Gate: `target/sparse-tiling-build-34.log`, including the end-to-end seven-tile
example with an empty residual. Builds 29–33 preserve intermediate proofs and
failures. CeTA term/source correspondence, certificate parsing and unified
production dispatch remain unfinished; no production executable changed.

The predicate is now exported directly by Isabelle to a diagnostic SML module
(gate `target/sparse-tiling-build-35.log`). Its unmodified generated code agrees
with native Ferrum construction on 84 small tilings and rejects 108 mutations
(192 checks total). Evidence and artifact hashes are recorded in
`target/sparse-tiling-export-35/crosscheck.json` and `native-crosscheck.log`.
This diagnostic export does not change the production checker executable or
complete CPF integration.

The separate `Sparse_Tiling_Source` session now connects the string theorem to
AFP's genuine first-order terms and rewriting relation. It proves that every
rewrite using unary rules with the same variable tail on both sides decreases
a multiset of branch strings, including arbitrary term contexts. Consequently
string termination implies termination of those term rules. The reverse
transfer, from an embedded term-system proof to word-system termination, also
passes. These proofs allow separate variables per rule and do not assume that
substitution instances or surrounding terms are unary.

Gate: `target/sparse-source-build-6.log`; the source is
`thys/Sparse_Tiling_Source/Sparse_Tiling_Source.thy`. A private session build
uses an explicit 29-directory AFP dependency closure, recorded in
`target/sparse-source-dependencies.json`. Attempt one missed a sibling session
dependency; attempts three and five preserve proof/syntax failures. The final
session has no admissions. Executable source-rule extraction, certificate
parsing and unified production dispatch remain pending. No production checker
executable changed.

`Sparse_Tiling_Extraction` now verifies executable extraction of unary terms
and rule lists, preserving a common variable tail within each rule. It proves
the composed `sparse_check_term_tiling_sound` theorem: finite tiling checks
against extracted source/residual rules and termination of the residual term
system imply termination of the source term system. Gate:
`target/sparse-source-build-10.log`, including SML compilation, rejection of
mismatched variable tails, branching and constants, and an end-to-end term
example using different variables in its two source rules. Attempts seven
and eight preserve intermediate proof failures; no admissions are used.

The residual's mathematical symbols are still tile lists. A verified finite
encoding into CPF function symbols, certificate parsing, and unified dispatch
remain pending. The production checker executable is unchanged.

`Sparse_Tiling_Encoding` now proves a finite tile-symbol encoding sound. Every
required tiled rule must encode to a rule present in the supplied residual,
and missing symbol mappings are rejected. The composed
`sparse_check_encoded_tiling_sound` theorem consumes ordinary first-order
source and residual rules, removing the earlier requirement that the residual
checker directly use list-valued function symbols. A homomorphic simulation
justifies the encoding; termination of the encoded residual is still required.

Gate: `target/sparse-source-build-13.log`, including SML compilation, a
positive encoded term example, missing-symbol/wrong-residual rejections and
deterministic handling of duplicate table entries. Attempts 11–12 preserve
proof/type failures. CPF parsing and unified processor dispatch are the next
integration steps. No production checker executable changed.

Unified sparse-tiling integration is in progress. The proposed `Sparse_Tiling`
termination-proof constructor contains finite closure data and one explicit
ordinary-TRS child proof. The processor requires empty Q and no weak rules;
it checks extraction, closure and tile-symbol encoding before returning the
residual. Its soundness case is part of the ordinary termination-proof checker,
not a standalone acceptance path. The current proof-base build has not yet
passed (`target/sparse-proof-base-build-2.log`); these changes are not release
checker evidence.

The proposed CPF extension `sparseTiling` contains, in order, `leftBorder` and
`rightBorder` symbol lists; `tiles` containing `tile` symbol lists;
`tiledRules` containing `tiledRule` entries whose `lhs` and `rhs` contain tile
lists; `tileEncoding` entries pairing a tile with an ordinary function symbol;
the residual `trs`; and its `trsTerminationProof`. All symbols use the existing
symbol parser. Missing encodings, insufficient residual rules and failed child
proofs must be rejected. This grammar is an implementation candidate, not a
claim of an upstream CPF standard revision. Parser/export and end-to-end
mutation gates remain pending. No generated production checking logic changed.

Native CPF integration fixtures are prepared by
`scripts/check_sparse_tiling_native.py`. The current preparation produces two
positive native artifacts (empty and nonempty residual) and seven semantic
mutations: missing closure tiles, mismatched source tails, an empty source left
side, a missing tiled rule, a missing used encoding, a false empty child proof,
and removal of required encoded residual rules. Preparation evidence is
`target/sparse-native-mutations-1/manifest.json`; **no checker was run**.

Once regenerated, the same unified checker must accept both positives and
reject every mutation twice. The script records certificate/checker hashes and
keeps `checked: false` until all checks pass. It requires unified category
dispatch including ITS, and has no standalone checker fallback. This gate
remains pending while the proof-base and parser builds are incomplete.

The unified **Proof_Checker_Base gate now passes** in
`target/sparse-proof-base-build-2.log`: the new processor wrapper, the
`Sparse_Tiling` proof constructor, residual recursion, assumption traversal and
the full termination-checker soundness proof are verified together. The build
completed in 41m16s including uncached dependencies; the proof-base session itself
took 3m09s. Attempt one remains preserved as a duplicate-session metadata failure.
This proves source-level integration into the common termination checker.
CPF parser compilation, regenerated exports and the native artifact/mutation
gate are still pending, so no production checker acceptance is claimed.

The first full parser dependency build fails before parser compilation:
`target/sparse-parser-build-1.log` identifies an imported-name collision in
`CSR_Minimal_CSDP_Proofs.csrewrite_complete`. The new RFC constructor's short
name `rewrite` shadows the existing executable rewriting theorem. Its name is
changed to `sparse_rewrite`, including the two local uses; the mathematical
statement and existing CSR proof are unchanged. The repeat gate is running in
`target/sparse-parser-build-2.log`. This is an integration defect, not a checker
rejection of a certificate. No executable export has been replaced.

The full `Proof_Checker` parser dependency gate now passes in
`target/sparse-parser-build-2.log` (23m36s including rebuilt dependencies;
Proof_Checker 5m50s). `CPF_Proof_Parser` verifies with the new `sparseTiling`
constructor, and the existing CSR theories pass after the RFC constructor
rename. This verifies parsing and formal checker integration together, not an
executable artifact acceptance claim.

The next gate regenerates `Certificate_Performance_CPF_Export` using the
unchanged production export interface and optimization theory. Catalog dry run
one selected a stale local AFP duplicate with a missing document file; its log
is retained. Dry run two resolves AFP duplicates to the pinned AFP tree while
retaining local checker sessions and reports the target dependency closure
(`target/sparse-cpf-export-dry-run-2.log`). Its nonzero dry-run status reports
unbuilt sessions, not a completed export. Generated production logic and the
unified executable remain unchanged until export and native mutation gates pass.

The complete `Certificate_Performance_CPF_Export` build now passes in
`target/sparse-cpf-export-build-1.log` (31m09s including dependencies). The
unchanged Isabelle export mechanism extracted the generated Haskell into
`target/sparse-cpf-export/`; extraction passed and its public API matches the
existing production boundary. The new deterministic snapshot is
`tests/unified/exports/cpf-sparse-tiling.tar.gz`, SHA-256
`0eb29f891a70b2fffc9895cd53aa05fdfadbdbcd2be0bca74acced41f1e19919`.
Only the CPF entry in the unified export manifest changes. The source snapshot
is `04e8417`; no generated checking logic was edited.

The unified O2 executable build is running in `target/unified-sparse-tiling-1`
with a persistent temporary directory and four library workers. The native
artifact/mutation gate is queued after a successful build receipt; neither
executable acceptance nor a production release is claimed yet.

The unified O2 build and native artifact gate now pass. Executable
`target/unified-sparse-tiling-1/ceta` has SHA-256
`291c79920562c4aaf5aaaa00eecc193876e3c4e60bed4e9689f4bb40bafc1259`.
`target/sparse-native-checked-1/manifest.json` records all 18 successful checks:
two native positive certificates accepted twice each, and seven semantic
mutations rejected twice each. This is one unified executable with all eight
category dispatch entries, including ITS; no fallback checker was used.

Existing dispatch, CSR removal/GM composition, GM04 source-map and retained CPF
semantic-negative gates also pass with the same hash. Commands, outcomes and
timings are in `target/sparse-existing-paths-1/results.json`. These focused
integration gates clear native sparse-tiling strategy activation in Ferrum.
They do not establish full-frontier retention or authorize promotion as an
already validated production release.

An isolated `Sparse_Tiling_Removal` session now verifies the word-level sparse
rule-removal variant from [Geser, Hofbauer and Waldmann, FSCD 2019, Algorithm
5.4](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2019.21).
The original rules supply forward-closure coverage; the retained subset must
contain every rule admitting an accepted redex. The proof transfers each
reachable rewrite to the retained system and then uses the already verified
RFC termination criterion. It does not assume global absence of the removed
left sides.

`thys/Sparse_Tiling_Removal/Sparse_Tiling_Removal.thy` includes the executable
`sparse_check_removal` and its soundness theorem, SML compilation, an empty
residual example, and rejection of a false empty residual with a live rule.
Gate `target/sparse-removal-build-5.log` passes; attempts 1–3 preserve proof/type
failures, and attempt 4 verifies the intermediate mathematical and live-rule
checking layer. No admissions are used. Term/source extraction, CPF constructor
and parser integration, generated export and unified native mutation tests for
this new variant remain pending. The frozen `291c799...` checker has not changed.

The isolated term/source gate for sparse rule removal now passes:
`target/sparse-removal-source-build-2.log`. The new
`Sparse_Tiling_Removal_Source` session composes checked unary source extraction,
word-level closure/removal soundness and transfer back to unrestricted ordinary
term rewriting. Its SML checks cover empty and nonempty retained systems,
changed source variable tails, an empty left side and a false empty residual.
Attempt one preserves ambiguous test-variable types; the theorem itself was
not weakened.

Common-checker integration is now proposed through `Sparse_Removal_Info`,
`sparse_removal_tt` and the `Sparse_Rule_Removal` proof constructor. It requires
empty Q and no weak rules, preserves assumption traversal and reconstructs one
ordinary termination child. CPF `sparseRuleRemoval` contains left/right borders,
closure tiles, tiled rules, the retained `trs` and its `trsTerminationProof`.
The full `Certificate_Performance_CPF_Export` build is running in
`target/sparse-removal-cpf-export-build-1.log`. Its dependency closure is pinned
in `target/sparse-removal-cpf-export-dependencies.json`. This integration and
export are not yet verified; no generated production archive or executable has
been replaced. The earlier frozen sparse-tiling checker remains unchanged.

The native mutation harness now accepts `--family removal`. It prepares two
new native positives and seven mutations, including removal of a live residual
rule and alteration of a retained rule outside the source system. Preparation
passes in `target/sparse-family-removal-prepare-2`; attempt one preserves a
fixture XPath mismatch and ran no checker. The default tiling family's nine
certificate hashes are unchanged (`sparse-family-tiling-prepare-1`). Native
rule-removal acceptance/rejection checks remain pending the regenerated unified
executable; fixture preparation is not certification.

## 2026-11-04 sparse rule-removal verified export

The restored `Certificate_Performance_CPF_Export` build finished successfully
on October 31 in `target/sparse-removal-cpf-export-build-2.log` (42m13s).
The first attempt remains preserved as an invalid storage-interruption run:
its `SQLITE_READONLY_DBMOVED` failures followed detachment of `/work/dfm`.

The verified common-checker and CPF integration is now exported without editing
generated Haskell. The source revision is
`96ce519d198a0f0d66a615417821ce50b293d11f` on `codex/policy-sparse-tiling`
in `CeTA-policy-eval`; the formal implementation was introduced in `0071826`.
The public generated-module API check passes. The deterministic source archive
`tests/unified/exports/cpf-sparse-removal.tar.gz` has SHA-256
`ec94cbbd3a548c2542561462993dfd80c4fd5108e5fe8227e0eb908f7bad92c7`.
The unified export manifest changes only the CPF source/archive provenance.
Extraction and source hashes are recorded in
`target/sparse-removal-export-package.json`.

The unified O2 executable is building in `target/unified-sparse-removal-1`.
Native positive/mutation checks for both sparse families and existing checker
regressions remain pending. This verified export alone is not a production
release or a full-frontier checker compatibility claim.

The unified O2 executable now builds successfully. Its immutable SHA-256 is
`ded2b82106725b442498cd050f15257a72975e115140c25625d928415bbb53f7`.
Both sparse families pass their two positive and seven semantic mutation cases,
each checked twice (36 total checks), with this same executable. The dispatch,
CSR composition, GM04 source-map and retained semantic-negative regressions also
pass. Evidence: `target/sparse-removal-checked-{tiling,removal}-1/manifest.json`
and `target/sparse-removal-existing-paths-1/results.json`. Generated logic remains
unchanged from Isabelle export. These gates establish native checker integration;
the complete protected frontier still requires its release replay.

## Main merge and Prolog preservation, 2026-11-05

Merge `b8b15c5` integrates main `76aaf02` into
`codex/prolog-production-integration` in `CeTA-prolog-release`. The isolated
`make ceta` build `target/unified-main-371/ceta` has SHA-256
`c93d34b487807b2f9c2ea25cc3b8a60933aebfce783d8bcdd1199ab24dba288e`.
With Ferrum `ef9e8b5`, complete strict replays retain 59 Prolog YESs and four
NOs, plus 84 cut YESs and nine NOs. Each retained proof passes original-source
audit, two checks with this executable and receipt authorization. Ferrum
`e777a7a` pins evidence in `docs/data/prolog-main-merge-20261105.json` and its
adjacent archive. No generated checker logic was edited. The guarded composition
lemmas remain unexported; no arithmetic benchmark gain or production promotion
is claimed by this merge.

## Checked guarded source graph, 2026-11-05

`LP_Prolog_Finite_Guarded_Graph` and `LP_Prolog_Finite_Guarded_XML` compose
the established finite regions and nested Splits with checked guarded call
descent and an integer child. The graph checks all referenced modules, retains
the original structural call/success receipts, and adds separate guarded
dependency receipts. Helper-return facts come from existing actual-source
integer, ground and combined shape receipts. Continuation descent uses actual
successful substitution, not arbitrary abstract residual answers.

Argument projection preserves every call edge and all guards/helper premises.
Duplicate and out-of-range positions are rejected. Six regression lemmas cover
selection order, malformed positions, retained guards/helpers and self-calls.
The numeric child is bound to exactly the projected observed relation; its
transfer table must match the source graph's. Original profile/query and source
program fields remain explicit. No new operational semantics or SEG is added.

The full dependency audit and XML soundness theorem pass in
`target/prolog-guarded-xml-387.log`, with only the two inherited checker oracles.
[Sources and all verification attempts](data/prolog-guarded-graph-20261105.json)
are pinned. This is not yet exported into the unified executable or assembled by
Ferrum; it certifies no additional benchmark root. Native assembly, fresh
positive certificates, mutations and replay remain required.

## Guarded Prolog export and unified validation

The verified guarded checker is now exported by Isabelle and registered in the
unified LP adapter. Generated shared helper modules are byte-identical to the
previous archive; no generated checking logic was edited. The isolated unified
checker at `target/unified-guarded-389/ceta` has SHA-256
`63439dfcaa4f474083c65b6c4127bc217732bb314837362f5fcf7b21b1888986`.
[Export and build evidence](data/prolog-guarded-export-20261105.json).

Ferrum validates three native fixtures including actual helper returns across a
Split, with strict state-local replay and missing-child/conflicting-advice
controls, four semantic negatives and 55 mutation checks. Fresh replay retains
59 YES + 4 NO Prolog and 84 YES + 9 NO LP-with-cut using this same checker.
This establishes integration and preservation, not a new benchmark gain or
protected-category production promotion.

## Exact arithmetic NO simulation foundations, 2026-11-05

The shared recurrent simulation contract now requires positive source progress
and preserves complete saved stacks. Ground first-clause resolution supports
fresh body variables. Interpreted integer assignments and guards compose in
source order; dispatch requires an ordinary defined predicate. The complete
iteration and nontermination consequence verify in
`target/prolog-recurrent-simulation-415.log`, without admissions or oracle
dependencies. This uses the existing LP-with-cut and interpreted Prolog source
relations, not a second operational semantics.

No new checker constructor or export is installed. Exact integer-child binding,
original source/profile/query checking and executable reconstruction remain
pending. Ferrum's native diagnostic child passes two unified checks and strict
controls, but adds no source verdict. The frontier remains 61 YES + 4 NO.
[Source snapshots, all verification attempts and child evidence](../../ferrum-prolog-release/docs/data/prolog-integer-recurrence-development-20261105.json)
are pinned with their archive. The unified checker remains `63439dfcaa4f474083c65b6c4127bc217732bb314837362f5fcf7b21b1888986`.

## Exact recurrence relation and LTS inverse, 2026-11-05

The ordered source recurrence now has a symbolic integer relation with verified
substitution, exact guards and exact recursive output values. The inverse
requires complete output length and literal/known-variable endpoints, and
transfers a child NO into actual source execution with saved alternatives.
The shared ITS LTS bridge supports arbitrary well-typed valuations; unobserved
Boolean coordinates are not required to be false.

Verification and dependency audits pass in
`target/prolog-recurrent-relation-435.log`, with no admissions or oracle
dependencies. [Pinned source snapshots and all attempts](../../ferrum-prolog-release/docs/data/prolog-integer-recurrence-relation-20261105.json)
include the stopped expanding-simplifier attempt 434 and native four-root
cohort. The full 221-root applicability scan finds four candidates; only `et1`
has an accepted integer NO child. The other three are integer-domain controls,
not source YESs; binary64 stagnation candidates remain separate obligations.

The source-to-child coordinate map, original source/profile/query binding,
executable parent constructor, XML and export remain pending. No generated
checker or unified executable changes, and no new source result, are claimed.

## Source integer recurrence NO, 2026-11-06

CeTA `be3ba51` in `CeTA-prolog-release`, branch
`codex/prolog-production-integration`, adds the verified
`prologIntegerRecurrenceProof` constructor. It checks first-clause selection,
ordered assignments/guards, exact recursive outputs and coordinate transport,
then invokes the existing common ITS NO checker on the exact relation.
The source simulation uses the shared operational semantics and preserves
saved alternatives. It does not use termination overapproximations for NO.

XML verification 448 and corrected export 451 pass their dependency audits.
The unified O2 build `target/unified-recurrence-453/ceta` has SHA-256
`3db3147cdfdeae982fc924fb2b8134bfe4a342521f05842fb55e9f9ed64ea751`.
Failed build 450 exposed an array code-printing import collision; the new code
setup restores the existing CeTA mapping before regeneration. No generated
checking logic was edited, and all previous LP modules/helpers retain their
bytes. Shared ITS changes qualify the solver default and separate standalone
export from parser import without changing the checking rules.

Ferrum `3bf839d` passes three native/strict positives, 15 semantic/advice
controls and 30 certificate checks. Complete strict Prolog replay retains
61 YES + 5 NO on 221 roots, gaining one source NO, and cut replay preserves
84 YES + 9 NO on 112 roots using this same executable. Every retained result
has an original-source audit, two checks and an authorized complete receipt.
[All attempts and integration evidence](../../ferrum-prolog-release/docs/data/prolog-integer-recurrence-integration-20261106.json)
pin sources, exports and checker build receipts. The protected-category
production promotion gate remains separate and open.

## Original-query arithmetic call NO integration, 2026-11-06

CeTA `5798b9b` in `CeTA-prolog-release`, branch
`codex/prolog-production-integration`, integrates the verified
`prologIntegerCallsProof` constructor. Formal development `4a165ed` binds exact
integer call rows, ordered earlier-clause failures, variable interfaces and
original-query entry reachability to the existing shared ITS NO checker.
The source simulation uses the established Prolog semantics and saved stacks.

Export 491 and typecheck 492 pass; unified O2 build 494 has SHA-256
`b649c1db9911948f07bbdb6bbd4f2d6c9f87c1352c73a890073628b7d4e5a3b8`.
All previous LP modules and helpers retain their bytes. Ferrum `3a953d9` passes
three native/strict positives, 18 semantic/advice controls and 31 certificate
checks. Complete strict replay retains 61 YES + 6 NO on 221 roots and cut
preservation retains 84 YES + 9 NO on 112 roots using this same executable.
All retained results have source audits, two checks and authorized receipts.
[Pinned integration evidence](../../ferrum-prolog-release/docs/data/prolog-integer-calls-integration-20261106.json)
includes the rejected raw-predicate reconstruction and its native encoding
repair. Matched superiority and protected-category promotion remain open.

## Partial arithmetic source steps, 2026-11-06

Formal development `a5a56d5` verifies fresh head resolution for arbitrary actual
arguments and pending goals, partial integer prefixes, failed-clause restoration
and ordered recursive-call progress. A negative theorem rules out capturing
caller variables in fresh clause locals. Verification 510 and its dependency
audit pass without admissions or oracles. The prior failures and incremental
checks are [pinned with source snapshots](../../ferrum-prolog-release/docs/data/prolog-partial-source-steps-20261106.json).

No generated checker or unified executable changed. Executable partial call
interfaces, original-query binding and native assembly remain pending. The
certified frontier stays 61 YES + 6 NO; this formal step claims no new root and
does not complete the superiority or protected-category promotion gates.

## Partial integer calls integrated and replayed, 2026-11-06

Formal commit `fce3fc0` and integration `f1ec3a4` add the checked partial-call
XML constructor, preserving actual unobserved arguments, fresh clause variables,
pending goals and every ordered alternative. XML verification 518, export 519
and Haskell typechecking 520 pass. Unified O2 build 521 has SHA-256
`493dfec3896b7e71aa0819927e42b580d20de32ce7401c631647ad577858eab3`.
All prior LP modules and shared helpers retain their bytes.

Ferrum `8f00d3e` integrates native reconstruction and shared recurrent-region
alternatives. Four native/strict positives, 21 semantic/advice controls and 40
certificate checks pass. Full replay retains 61 YES + 7 NO, adding rec-counter;
cut preservation retains 84 YES + 9 NO with the same immutable checker. Every
retained result has source audit, two checks and an authorized receipt.
[Pinned integration evidence](../../ferrum-prolog-release/docs/data/prolog-partial-calls-integration-20261106.json)
includes failed attempts and the shared cycle test assertion issue. Matched
superiority and protected-category production promotion remain open.

## Guarded arithmetic helper returns, 2026-11-06

`LP_Prolog_Guarded_Helper_Return` extends the actual helper return theorem with
a checked prefix of arithmetic guards and fresh local assignments. The final
assignment can bind a caller output. Its substitution reaches every active
continuation alias, while saved alternatives keep their original terms.
Original clause matching, ordered earlier-clause failures, observed integer
inputs, successful guards and an unassigned caller output are explicit
premises. This uses the existing source semantics and partial-prefix theorem.

Gate 526 exposed a missing normalization of bound arithmetic goals; gate 527
passes the complete theorem and admission/oracle audit from heap 525. The
verified child heap is `target/prolog-guarded-return-527.heap`. This theorem has
not yet been exported into an executable source constructor. The unified
checker and certified benchmark frontier are unchanged.

## Exact helper recipe and continuation composition, 2026-11-06

`LP_Prolog_Helper_Return_Recipe` supplies an executable Boolean check binding a
finite arithmetic helper recipe to its complete unique source clause, signature,
head variables, input requirements, prefix and final output expression. Its
soundness theorem constructs the actual source return with arbitrary pending
goals and saved alternatives. Integer observations, fresh caller output and
successful prefix guards remain state premises. This is an exact-call proof
component, not a universal return summary or a graph termination certificate.

`LP_Prolog_Helper_Return_Continuation` composes the returned binding with a
successful or failed caller comparison. Success retains every helper
alternative. The failure rule requires that only the helper barrier remains
above the caller's saved stack; it cannot skip later helper answers. The final
state is the original saved stack without the helper's successful bindings.

Gate 528 verifies continuation composition. Gates 529–531 record a recipe
parsing failure; diagnostic 532 records an incorrect relative import, and 533
isolates missing whitespace after the subset symbol. Gate 534 verifies the
recipe theorem and five controls: a positive renamed helper and rejection of
an extra clause, missing integer input, bound output and missing body. All
admission/oracle audits pass. Executable source-row integration, export and
benchmark certification remain outstanding; unified checker 521 is unchanged.

## Helper recipe parent parser, 2026-11-06

`LP_Prolog_Helper_Return_Recipe_XML` parses the source recipe fields for use
inside a parent certificate. The original program remains a parameter of the
verified recipe check. No standalone verdict or checker dispatch was added.
Gate 535 records a lexical error caused by adjacent `=ops`; gate 536 verifies
the corrected parser. Native discovery and serialization use the same field
order. This is not yet a complete parent certificate or an export update.

## Actual helper call interface, 2026-11-06

`LP_Prolog_Helper_Call_Interface` binds the source recipe to actual arguments
through the existing partial-call interface. Its checked positions must cover
exactly the recipe's integer input variables, with a distinct head and a valid
output position. Observations concern actual integer values, not source terms
that might evaluate to integers. An actual variable at the output position and
successful guards yield a checked source return on the whole caller
continuation. Gate 537 passes the theorem and dependency audit.

This theorem preserves the fresh caller renaming introduced by resolution.
Source-row composition must transport that renaming and the returned binding;
replacing a helper call with flattened arithmetic instructions is insufficient.
The existing unified executable and certified root count are unchanged.

## Caller environment transport after helper returns, 2026-11-06

`LP_Prolog_Helper_Caller_Environment` composes the actual helper return with
the caller's remaining source body and external pending goals. Its environment
includes both the fresh caller renaming and the output substitution. Saved
alternatives remain outside that transformation.

`LP_Prolog_Helper_Caller_Context` supplies a shared invariant for numeric
observations and unused local names. It initializes from the established
partial-call environment, preserves known integers through assignments and
helper returns, and retains distinct fresh names for later local assignments.
Unobserved head arguments remain arbitrary actual terms. The accompanying
primitive lemmas justify source comparisons and assignments in the updated
environment using the existing source rules.

Gate 544 verifies all three theories and their dependency audits. Attempts
538–543 retain missing extensional normalization, a global `args` collision,
bound-goal normalization, reserved fact-label errors and an ambiguous theorem
instantiation. No unchecked assumption, alternative source relation or checker
export was introduced. The next assembly step is the checked sequence of
arithmetic operations and helper calls, using these invariants.

## Checked arithmetic/helper prefix sequences, 2026-11-06

`LP_Prolog_Helper_Prefix_Check` defines a source-bound helper call site and
prefix operations that distinguish actual helper calls from primitive arithmetic.
Observed numeric inputs must be endpoint values matching the actual call terms;
output position, freshness, input types, recipe and interface remain checked.
The observation theorem connects these checks to the caller's actual values.

`LP_Prolog_Helper_Prefix_Steps` and `LP_Prolog_Helper_Prefix_Sequence` prove
execution of arbitrary finite checked prefixes in the existing source relation.
Each step transports the numeric context and pending goals. The proof retains
all introduced helper barriers above the original saved stack. It does not
flatten helper calls into replacement source instructions.

`LP_Prolog_Helper_Prefix_Failure` proves that a checked failed comparison after
such a prefix restores the original saved stack: successful substitutions do
not leak into resumed alternatives. Only the recorded helper barriers are
removed, using existing administrative source steps. The unique-helper recipe
check prevents skipping later helper clauses.

Gate 550 passes all four theories and dependency audits. Gate 546 first passed
the helper source step; failures 545 and 547–549 record a reserved label,
over-expansion by simplification and an unavailable list lemma. Source-clause
selection/failure receipts and executable call-row assembly remain outstanding.
The unified executable and certified root count are unchanged.

## Exact source calls with finite arithmetic helper returns

The new `prologHelperIntegerCallsProof` constructor composes checked finite
helper returns with original clause selection, ordered failure alternatives,
partial integer interfaces and pending continuations. Its numeric child is
checked by the existing ITS checker. The soundness proof uses the existing
Prolog execution relation and does not infer nontermination from a termination
overapproximation. Helper success premises remain explicit in the transition.

Formal verification, XML export and Haskell type checking pass; isolated unified
build 563 has SHA-256
`2ee69961d5c63cb7d64547608bc017df6acc44234cb565519ca6a5088d5fbb6a`.
All existing generated modules and shared support files are preserved. The
[pinned checker evidence](data/prolog-helper-call-checker-20261106.json) retains
failed proof attempts as well as successful verification. Native benchmark,
mutation and complete preservation replay gates remain pending at this point;
this record claims no additional certified root or production promotion.

The subsequent native integration gate passes: Ferrum `2ce74b2` certifies the
new Euler Fibonacci NO, and complete strict replay retains 61 YES + 8 NO with
69 authorized receipts. Cut replay preserves 84 YES + 9 NO with the same unified
563 executable. Four native/strict positives, 29 semantic/advice controls and
51 certificate checks pass. [Full source, mutation and replay evidence](../../ferrum-prolog-release/docs/data/prolog-helper-calls-integration-20261106.json)
pins checker integration `55f0e17`. Protected-category production promotion and
matched superiority remain separate open gates.

## Fixed numeric bounds without integer-type assumptions

The verified scalar-observation development separates a fixed numeric bound
from the type of a loop counter. Exact rational cross multiplication matches
Ferrum's mixed integer/binary64 comparison. Fraction floor/ceiling lemmas supply
integer bounds and a descending integer-counter rank. Binary64 source names
are injective within 64 bits, distinct from integer names, and substitution
preserves their values. Scalar fractions are unique; their floor observations
survive substitution without establishing an integer type for a float.

Verification 571, 572, 575 and 576 passes without skipped proofs or oracle
dependencies. The final control formally demonstrates that the existing finite
evaluation envelope permits distinct scalar results for one float. Consequently
it cannot justify a stable bound on its own. This is lost precision in the
existing overapproximation, not a claim that its earlier proofs are unsound.
A source bridge must retain successful evaluation, a stable result for the
original bound expression, comparison correspondence and actual Split returns.
Ground query arguments can be compound arithmetic expressions, not only scalar
literals. No floating update is assumed to advance.

The unified checker and certified frontier are unchanged. These theories are
not exported into a source-proof constructor yet. [Pinned development evidence](../../ferrum-prolog-release/docs/data/prolog-scalar-bound-development-20261106.json)
includes native threshold/stagnation tests and unsuccessful formal attempts.

## Stable arithmetic evaluation and actual returned values

The stable arithmetic development extends exact scalar observations to compound
expressions under one fixed partial operation interpretation. Successful results
are unique, finite ground and substitution invariant. The interpretation agrees
with the existing checked integer arithmetic fragment. It is a semantic parameter,
not a table accepted from a certificate; connecting the original profile to that
interpretation remains a source-bridge obligation.

Verification 585 checks comparison outcomes, integer compatibility, retained
errors and bounds derived from successful comparisons. Verification 587 checks
`is/2` successful substitutions using the existing scalar unifier, plus refinement
of the existing parameterized source execution relation. Neither introduces a
replacement SEG or execution relation. These checks have no skipped proofs or
oracle dependencies. Attempts 584 and 586 retain the failed propositional proof
and missing import, respectively. The earlier 583 attempt was interrupted after
identifying expensive proof automation and replaced with explicit witnesses.

No checker export or native source-proof constructor has changed. The certified
frontier remains 61 YES + 8 NO; actual context initialization, Split contracts,
source-profile correspondence, residual assembly and replay still gate gains.

Verification 589 additionally checks substitution and source-expression transport
for strengthened comparisons in the existing observation datatype. It retains
every previous observation and does not initialize or transfer saved alternatives.
Attempt 588 records a corrected theorem-argument type mismatch.
[Pinned development evidence](data/prolog-stable-arithmetic-development-20261106.json)
archives the theory snapshots and all retained attempts 577–589. The remaining
source and Split obligations above are unchanged.

## Stable context facts through actual helper answers

Verification 591 proves substitution, context joining and preservation of stable
context facts through the shared actual-answer relation. Every incoming saved
frame must establish the context; helper termination alone is insufficient.
A separate theorem preserves the floor of an actual successful evaluation across
helper answers. The proof retains the existing context tuple and all its facts,
guards and observations. Attempt 590 records a corrected context-normalization
proof, not a changed semantic premise.

The next assembly work must initialize these observations at successful source
operations, check module interfaces and retain saved alternatives separately.
The existing finite guarded graph still uses its previous context interpretation;
these lemmas do not silently strengthen that graph's assumptions. No root gain,
checker export or production promotion is claimed here.

Verification 594 proves the projected expression bound is exact for successful
evaluation, stable for a captured ground expression, and preserved through actual
helper returns with initialization on every incoming frame. A successful ordered
comparison yields an upper bound on an independently typed integer counter.
The projection does not coerce the source expression to an integer. A fixed
fallback coordinate for non-evaluable expressions yields no comparison fact.
Attempts 592–593 retain a theorem-instantiation ambiguity and substitution rewrite
orientation error, both corrected without weakening the statements.

Verification 596 checks initialization from actual successful comparison and
`is/2` outcomes, using the existing context-addition operation and unifier.
The `is/2` theorem applies its actual substitution to the entire prior context
before adding the evaluation observation. Attempt 595 records a reserved
Isabelle fact-label error. All successful gates reject skipped proofs and oracle
dependencies. [Pinned return/bound evidence](data/prolog-stable-return-bound-development-20261106.json)
retains every attempt 590–596 and the checked theory snapshots.

Next, checked link transport must retain the stronger comparison semantics;
ordinary finite-comparison transport alone does not establish it. The referenced
module source proof must use the stable builtin interpretation, with the original
source profile covered and all failure/error paths retained. Native bound
coordinates then enter the common ITS residual under these checked receipts.
Existing guidance atoms, checker executable and benchmark counts are unchanged.

## Stable observations on existing return links and Splits

Gate 602 verifies that the existing evaluation-context transport receipts suffice
for stable arithmetic comparisons. The apparent additional comparison check is
proved equivalent to the existing transport checker: it already requires the
substituted comparison to occur in the source observations. Thus this extension
does not discard context or narrow accepted transport receipts.

The stable return-link theorem retains the existing link checker, normalized
equations, free knowledge, scope swaps, target context and descent interface.
The Split theorem instantiates shared actual-answer composition, preserving scope
separation and initialization on every incoming saved frame. Prefix termination
does not supply return facts. No second operational semantics or SEG was added.

[Development evidence](data/prolog-stable-link-split-development-20261106.json)
pins all attempts 597–602 and the verified theories. Earlier attempts record a
substitution normalization failure, explicit transport-premise assembly, the
required shared variable type for summaries and contexts, and conjunction
elimination in a groundness proof. Gate 602 has no skipped proofs or oracle
dependencies. Native code, exported checker and the 61 YES + 8 NO frontier are
unchanged.

Next is arithmetic-node checking under the stable builtin interpretation within
the existing referenced-module graph. Complete source/profile coverage and native
bound-coordinate projection remain necessary before residual discharge and fresh
mutation/full replay gates can count any benchmark gain.

## Stable arithmetic source outcomes and comparison nodes

Verification 603 connects the stable builtin interpretation to source `is/2` and
all comparison descriptors, including reversed operands. Error outcomes are
preserved exactly for these operations, and checked integer evaluation agrees
with the existing integer `is/2` interpretation.

Verification 609 covers actual arithmetic answer transitions and the established
comparison-node checker. Success carries its stable observation through the
existing success link. Failure resumes the saved alternative, and uncaught error
clears the stack. The same three-link receipt, scope swaps, ground/free knowledge
and graph tables are retained. The representation strengthens the interpretation
of existing contexts; it does not construct a replacement graph.

Attempts 604–607 retain outcome-normalization and identity-substitution proof
failures. Attempt 608 was explicitly interrupted after identifying a proof rule
that reapplied itself to the same success fact; a direct case proof passes in
609. No semantic premise or source branch was removed to fix those scripts.
The source comparison operation now has a checked stronger context path, but
`is/2` node assembly, the remaining graph nodes, module contracts, original-profile
coverage and native bound projection still gate benchmark gains. The exported
checker and the 61 YES + 8 NO frontier are unchanged.

Gate 610 rechecks the final arithmetic-step and comparison-node theories and adds
the existing finite-domain obligation under the stable context interpretation.
All successful gates have no skipped proofs or oracle dependencies.
[Pinned arithmetic-node evidence](data/prolog-stable-comparison-node-development-20261106.json)
archives every attempt 603–610 and the final theory snapshots. The next `is/2`
assembly target is `LP_Prolog_Finite_Observed_Is` and its shared equality
normalization; stable evaluation evidence must survive the fresh-result and
actual-unifier interface there.

## Actual `is/2` results, resolution and equality with stable contexts

Gates 611–615 pass the next source-node integration batch without skipped proofs
or oracle dependencies. Stable `is/2` normalization uses the existing scalar MGU
and shared equality transition, retaining unification failure and uncaught error.
The established observed-`is/2` receipt introduces a fresh result variable, carries
its actual stable evaluation, and checks the middle equality link before using
its child contract. No intermediate equality state is treated as an already
completed Prolog operation.

Fresh-variable environment congruence, resolution refresh and the existing forked
context operation preserve both active and old bindings. The resolution and
equality theorems reuse their existing receipts, including free-variable rational
unification coverage, success/failure specialization modes, scope separation,
actual return values, newly established equations and untouched free variables.
The failed branch retains its original context and saved alternatives.

[Pinned development evidence](data/prolog-stable-is-resolution-development-20261106.json)
archives every gate 611–615 and the verified theory snapshots. This remains
source-proof development: the remaining node rules, complete referenced-module
contract, original-profile correspondence and native bound projection are not yet
integrated. No export, guidance atom or production checker changed; the certified
frontier remains 61 YES + 8 NO. Full semantic mutation and strict replay gates must
precede counting any new benchmark result.

## Established primitive-action integration with stable contexts

Gates 616–620 verify administrative transitions, clause allocation, meta-calls,
ordinary cut actions, integer tests, identity, term tests, both disequality rules,
and probe operations. The combined theorem uses the existing primitive-action
checker and receipts. Source transitions refine the previous builtin envelope;
no new source execution relation or graph constructor was introduced. Successful
integer tests add integer facts; groundness alone still does not establish them.

Gate 624 proves that stable contexts imply the legacy finite context, by induction
over actual finite helper-success derivations and their guards. This implication
reuses the existing primitive-domain checker while the new source proof retains
its stronger context representation. It is not a context reset. The combined
primitive soundness and domain obligations are now verified.

[Pinned primitive evidence](data/prolog-stable-primitive-development-20261106.json)
retains all attempts 616–624. Attempt 621 records a variable-name collision, 622
an unfinished guard-transfer proof, and 623 was interrupted after identifying
expensive proof automation. The explicit induction in 624 passes. All successful
gates reject skipped proofs and oracle dependencies.

Specialized module actions (including length, constant evaluation and equation
rewrites), full referenced-module assembly, original-profile coverage and native
bound projection remain outstanding. No checker export or guidance changed, and
no benchmark gain is claimed: the frontier remains 61 YES + 8 NO. Semantic mutation
controls and complete strict replay remain required before any gain counts.

## Stable module actions, control contracts and observed triples

Gates 625–626 verify constant `is/2` and length normalization using existing
receipts and shared equality. Length keeps its existing finite-result semantics;
this development does not assign a structural measure to a cyclic spine.
Gate 628 checks the remaining module-action cases: equation and clause rewrites,
finite comparison/evaluation errors, trimming, parallel saved alternatives,
refuted contexts, evaluation and length. Finite-error contracts transfer through
an explicitly proved transition refinement that preserves termination and every
actual answer. Gate 627 retains the unfinished automated path-coverage proof;
628 uses explicit inclusion of paths and emitted answers.

Gate 629 verifies complete local control contracts, including separately checked
local context strengthening, all boundary obligations, invariants, scopes and
emissions. Gate 630 connects these contracts to observed triples and actual-return
model obligations. The existing control tables, checks and receipts are reused.
The stable triple contract instantiates the shared answer contract with the
stable builtin interpretation; it does not define another operational semantics.

[Pinned control-development evidence](data/prolog-stable-control-development-20261106.json)
archives every attempt 625–630 and the final theories. Successful gates have no
skipped proofs or oracle dependencies. Referenced-module region and Split parent
contracts, original-profile coverage, native bound projection, residual discharge
and mutation/strict replay remain outstanding. No export or guidance changed;
the certified frontier remains 61 YES + 8 NO.

## Stable parent composition and checked helper returns

Gates 631–633 and 635–638 verify actual-answer triple contracts, checked
instance interfaces, guarded connections and regions, captured inputs, nested
Split composition, finite referenced-module induction and preserved-context
Splits. Existing graph tables, scopes, transport and return receipts are reused.
Every represented module must supply its local contract; a residual termination
proof cannot discharge helper returns or omit a dependency.

Gates 641 and 643 verify transition refinement for actual answers and reuse
existing integer, ground and shape return receipts. Strong arithmetic contexts
are preserved from initialized inputs; returned facts are established by the
existing analyses of actual successful execution. The finite envelope is used
only to reuse those analyses, not to replace the stronger parent context.
Combined return receipts now discharge the continuation-context premise of the
corresponding guarded Split contracts.

[Pinned parent and return evidence](data/prolog-stable-parent-returns-development-20261106.json)
retains attempts 631–643, including a constant-name collision, two unfinished
proof steps and a redundant copied proof corrected before the passing gate.
Successful gates reject skipped proofs and oracle dependencies. These are
source-proof development results: stable observed-call descent, checked numeric
bound projection, original-profile coverage, native assembly and export remain
unfinished. No checker binary or guidance changed. The certified frontier
remains 61 YES + 8 NO; mutation controls and complete strict replay are required
before counting any gain.

## Stable graph-root descent and bound-coordinate projection

Gates 644–646 connect the existing observed-call receipts to stable contexts,
region and Split descent, every component of the referenced graph, and the
source query root. The same established graph checker and receipts are reused.
The theorem concludes termination under the fixed compatible arithmetic
interpretation only after the complete stable call relation is proved terminating.
It does not supply that residual proof or original-profile correspondence.

Gates 647, 649 and 651 verify separate integer and upper-bound coordinates,
substitution and instance matching, coordinate valuation existence, and
argument projection preserving every call edge. Empty projections do not erase
recursive edges. Bound coordinates require ground source expressions and observe
the floor of their stable value; they do not assert that a float or compound
expression is an integer. Successful comparison remains required to constrain
the counter. Controls reject float counters and uninitialized bounds, and prove
that removing groundness permits a bound to change after substitution.

[Pinned graph/projection evidence](data/prolog-stable-graph-projection-development-20261106.json)
archives attempts 644–651 and theory snapshots. Two proof-development failures
are retained: unfinished groundness elimination and a reserved fact label.
Passing gates have no skipped proofs or oracle dependencies. The checked
ITS-row translation, source-profile binding, native assembly/export, residual
discharge and mutation/strict replay remain open. No checker binary or guidance
changed, and the certified frontier remains 61 YES + 8 NO.

## Checked upper-bound guards and source endpoints

Gate 658 verifies source-bound translation of successful less-than and
less-or-equal comparisons into an integer upper-bound condition and a typed
ITS formula. Counter expressions require established integer inputs. Bound
expressions retain their original source syntax and stable evaluation; they
are not retyped as integers. Distinct key constructors separate integer values
from bound observations even when both refer to the same source variable.

The endpoint checker separately binds each coordinate to its source term.
Integer endpoints retain the existing literal/variable restriction. Bound
endpoints require checked finite ground inputs. Formula soundness requires
assignments only for the finitely many keys used by that endpoint, allowing
the eventual row valuation to be constructed from finite bindings.

[Pinned bound-row evidence](data/prolog-stable-bound-row-development-20261106.json)
retains attempts 652–658, including naming collisions and unfinished proof
normalization steps. The successful dependency audit has no skipped proofs or
oracle dependencies. These guards and endpoints still need assembly into full
checked transition rows, valuation-extension proofs and the numeric-call
simulation. Original-profile binding, native export, residual discharge and
mutation/strict replay are also pending. The checker binary and guidance are
unchanged; the certified frontier remains 61 YES + 8 NO.

## Combined stable numeric conditions

Gate 660 verifies one checked condition interface for existing integer
evaluation/comparison receipts and new stable upper-bound comparisons. Both
produce formulas over the same distinct integer/bound keys. Integer operations
reuse the established numeric observation theorem through a proved stable-to-
finite observation refinement; groundness never supplies an integer premise.
The formula proof requires assignments only for keys actually used in the
condition.

[Pinned condition evidence](data/prolog-stable-numeric-conditions-development-20261106.json)
retains the successful audit and attempt 659, explicitly interrupted after
identifying expensive higher-order simplifier search. Gate 660 uses direct
operand equalities and has no skipped proofs or oracle dependencies. Complete
row assembly, finite valuation extension, transition simulation, original-
profile/native integration and strict replay remain outstanding. No checker
binary, guidance or certified count changed: 61 YES + 8 NO.

## Complete stable numeric rows and graph-root composition

Gates 670–673 verify complete path formulas, finite valuation bindings,
source-ground endpoint tuples, call-row typing, one-step ITS simulation,
termination of the entire stable observed-call relation, and composition back
to the established graph root. Every row binds input and output terms, coordinate
modes, source observations, transition locations and the actual child formula.
The valuation extension preserves all input coordinates and prevents auxiliary
bindings from overwriting recursive-call outputs. Ground endpoint evidence
comes from checked integer facts or source observations, not from an unsupported
integer interpretation of arbitrary ground values.

The existing ITS checker supplies the child termination theorem. All source
regions, Split dependencies and actual helper-return contracts remain checked
by the established graph assembly. Argument projection preserves call edges.
The new graph checker does not take an arithmetic-operation table from the
certificate: soundness is quantified over fixed compatible interpretations.
Binding this result to the original source profile is still an explicit next
obligation; the theorem alone does not establish native-profile coverage.

[Pinned numeric graph evidence](data/prolog-stable-numeric-graph-development-20261106.json)
retains attempts 661–673 and final theories. Failed attempts record proof
instantiation, finite key coverage, formula typing and notation errors. All
successful audits reject skipped proofs; local simulation rejects all oracle
dependencies, and the component/graph audits admit only dependencies already
inherited from the existing TRS termination checker.

Original-profile binding, XML/code export, native row generation, semantic
mutations, real residual discharge and complete strict replay remain unfinished.
No checker executable or guidance changed; the certified frontier remains
61 YES + 8 NO. Matched superiority and protected-category promotion remain open.

## Shared-budget stable evaluation development (2026-11-06)

`LP_Prolog_Stable_Fuel_Evaluation` checks successful recursive scalar
observations using one shared fuel budget across operands. Successful results
refine the stable scalar relation, consume budget, and agree across different
successful budgets. Budget exhaustion returns no observation and does not
establish finite source failure. The second-operand budget guard follows from
the proved strict consumption property of a successful first operand.

Attempt 681 passed with proof and oracle checks from the verified 673 heap;
[development evidence](data/prolog-stable-fuel-development-20261106.json)
preserves attempts 674–681. This is a semantic evaluator with a fixed operation
parameter, not a correspondence proof for the Rust implementation. Original
binary64/profile binding, source coverage, export, and native integration remain
open. No checker binary, guidance, or certified frontier changed (61 YES + 8 NO).

## Stable arithmetic profile and source XML export (2026-11-06)

The stable graph now has a fixed integer operation specification covering the
existing exact unary and binary integer fragment. The graph theorem requires
no certificate-supplied integer compatibility assumption. Operations outside
that fragment retain one fixed partial interpretation; binary64 terms cannot
be decoded as integers, and integer zero divisors produce no successful value.
This is not yet an audited correspondence proof for the native source profile.

`prologEstablishedStableSEGGuardedProof` binds the original graph assembly,
transfer contracts, contexts, referenced Split components, projected observations,
coordinate roles, complete numeric row receipts, and the common ITS child.
Its parser contains no operation-table witness. Old source constructors remain
unchanged. Isabelle verifies the source XML theorem and its dependency audit.
The generated `Prolog_Stable_Guarded_Generated.hs` passes GHC type checking;
shared generated support modules are byte-identical to the current LP manifest.

[Development evidence](data/prolog-stable-profile-export-development-20261106.json)
pins successful attempts 682, 683, 685, and 687, typecheck 688, the parser syntax
failure 684, and the container-instance export failure 686. Generated checking
logic was not edited. Unified dispatch, native stable-row synthesis, executable
mutation controls, original-profile auditing, and new certified root replay
remain open. No installed checker, guidance, or certified verdict changed.

## Unified stable graph checker candidate (2026-11-06)

`make ceta` builds the stable graph source constructor into the existing unified
Prolog dispatcher in isolated output `target/unified-stable-guarded-689`.
The executable SHA-256 is
`7305f8885688d6e737cf0e5449009342962420672afd1ab7470122ec99733b99`.
Every previous LP generated module and every non-LP library archive is unchanged.
The generated checking logic is exactly the verified export from `6dff126`.

The counter and Split source fixtures pass under the new constructor; 22
mutations reject missing child proofs, rows, type facts, descents, projections,
components, contexts, roots, child triples, wrong profiles and conflicting
coordinate roles. All 69 retained Prolog and 93 LP-with-cut certificates pass
two checks each using this same executable. The recheck validates frozen source
and certificate hashes, with four workers, two solver threads and 30-second
checker limits. This is certificate preservation, not a fresh native strict
replay or protected-category production gate.

[Pinned integration evidence](data/prolog-stable-unified-development-20261106.json)
retains build 689, fixture controls 690/693/694/695, successful recheck 692 and
the initial retention-harness schema error 691. Ferrum `1f1f8e2` separately adds
native stable condition receipts with three passing focused tests. Complete
native row generation, scheduler integration, stable-bound source audits and
benchmark gains remain open. No production promotion or new frontier is claimed.

## Stable source row diagnosis (2026-11-06)

Native bounded-loop certificates 1059/1060 remain rejected by unified checker
689. Diagnostic attempts 696–700 isolate two independent failures: numeric
observation coverage and the entry region's evaluation-context transport.
The ITS proof, transfer contracts, headers, endpoint roles, bindings and exact
transition formula checks pass. Diagnostics are not certificate verdicts.

The stable numeric row now selects evaluations and comparisons for arithmetic
condition receipts. Ground, equation and shape observations remain in the
source row and continue to justify checked context and endpoint evidence.
Attempt 699 reloads the changed row theory and verifies the call-step soundness
theorem with its dependency audit. Shared ground-link transport, regeneration,
unified checking, controls and fresh strict replay remain open. No certified
frontier or installed executable changed.

[Diagnostic and proof evidence](data/prolog-stable-row-diagnosis-20261106.json)
preserves the diagnostic wrappers, build failures and results.

## Checked ground knowledge across source links (2026-11-06)

The shared evaluation link now adds its already checked ground knowledge to
its source context before normalization and destination substitution. Both
the evaluation and stable link witness theorems prove the resulting context
from the existing knowledge premise. No integer, finite-spine or helper-return
fact is inferred from groundness. The original root context remains empty.

Attempts 704 and 705 verify the changed definitions from a pre-link heap and
rebuild the dependent stable proof. Attempts 701–703 preserve a missing
unfolding and two rejected attempts against a finished, stale imported theory.
[Pinned evidence](data/prolog-stable-ground-link-20261106.json) records the
verified sources and logs. Full source export, unified checks, semantic controls
and strict replay remain pending. No benchmark gain is claimed.

## Native stable-bound unified acceptance (2026-11-06)

Export 706 checks the complete changed source theorem and generates the stable
module. Unified build 707 has SHA-256
`8fab618f3bd0f300b4d09cef1a05a6832b3b3a5594a314e17eee80cc17b4ee91`.
All previous LP generated modules and non-LP library archives remain unchanged.
The native bounded-loop certificate passes twice and 14 mutations reject.
Recheck 710 preserves all 69 Prolog and 93 LP-with-cut certificates with two
checks each, original source/certificate hashes and the same executable.

Ferrum attempt 1061 additionally certifies two renamed fixtures by fresh native
search and strict authorized replay, with nine semantic/advice controls. The
four-root benchmark cohort 1062 reaches residual solving but remains UNKNOWN
on all four roots. This is no new benchmark gain, complete frontier replay or
production promotion. [Pinned evidence](data/prolog-stable-ground-integration-20261106.json)
includes the diagnostic wrapper, full export log, build and certificate checks.

## Stable structural/numeric routing development (2026-11-06)

The same observed call relation can now be partitioned by a checked natural
rank. Same-rank rows remain mandatory component obligations; cross-rank calls
must decrease. A finite coverage theorem bounds every row's source rank by the
component proof-table size. The structural bridge separately requires checked
finite-ground target arguments and child termination on those admissible calls;
it does not assume termination on arbitrary rational terms or infer return
contracts from termination. Ground output receipts use the existing path-type
and observation rules.

Attempts 717 and 724 verify these theorems and their dependency audits.
[Evidence](data/prolog-stable-routing-development-20261106.json) preserves every
failed proof attempt. This is a formal composition interface, not an exported
checker constructor or a benchmark gain. Native mixed-child assembly, actual
successful helper relation transport across Splits, XML integration, controls
and strict benchmark replay remain open.

## Stable relational helper returns (2026-11-06)

The stable source interpretation now instantiates the shared actual-return
model theorem. A successful helper call can be retained in the caller context
under checked source-program and builtin-model coverage. The saved-frame lemma
recovers the actual helper environment before adding the relation and preserves
incoming ground knowledge. It does not annotate failure alternatives or infer
a successful return from a termination proof.

Attempts 725 and 727 pass verification and dependency audits; failed attempt
726 is retained in the [evidence](data/prolog-stable-relational-return-20261106.json).
The Split interface, native assembly and exported checker still need to consume
this theorem. There is no new benchmark gain or changed unified executable.

## Relational Split composition (2026-11-06)

The checked stable Split interface now has relational-return composition
theorems for preserved groundness and newly returned groundness. The combined
receipt establishes both facts in the same actual helper-return environment.
Its helper success model must equal the parent model; local termination alone
cannot establish the relation. Both helper and continuation descent obligations
and the existing context/instance transport checks remain required.

Attempts 728–730 pass verification and dependency audits.
[Pinned evidence](data/prolog-stable-relational-split-20261106.json) records all
three runs. Executable constructor integration, native global model coverage,
mixed residual children, mutation controls and benchmark replay remain open.
No unified executable changed and no benchmark gain is claimed.

## Relational Split check and component wrapper (2026-11-06)

A Boolean check now binds the helper atom, success-model identity, ground return
receipt, continuation interface and both observed-call descent receipts. Its
soundness theorem discharges the relational Split composition obligations. A
new component wrapper supports that check alongside every existing finite
component/descent pair, reusing their stable soundness theorem.

Attempts 731 and 732 pass verification and dependency audits.
[Evidence](data/prolog-stable-relational-check-20261106.json) pins both theories
and logs. The whole-graph constructor, code export, native assembly and benchmark
validation remain open. No unified executable or certified frontier changed.

## Relational whole-graph and routed source soundness (2026-11-06)

The relational component table now has a whole-graph Boolean check and a
source-root soundness theorem. Initial query modes, empty initial context,
module coverage and context-table lengths retain their existing checks. A
compatibility theorem maps every accepted legacy graph to the new wrapper.
Finite SCC routing composes independently terminating component relations with
checked decreasing cross-component ranks into the same source-root theorem.

Attempts 733–735 pass verification and dependency audits.
[Evidence](data/prolog-stable-relational-graph-20261106.json) pins the theories
and logs. Backend-specific child certificate checks, native model/context
assembly, export, mutation controls and strict benchmark replay remain open.
No unified executable or certified frontier changed.

## Observed runtime queries for structural triple children (2026-11-06)

The existing PiDP checker now has a soundness theorem for runtime terms with
finite-ground evidence at selected query positions. Discarded arguments may
remain infinite or rational. The proof reuses the shared infinite-query
projection and PiDP chain theorem. A role-renaming bridge reflects the checked
child result to the source alphabet, preserving the same selected positions.

Attempt 742 verifies both bridges and dependency audits. Failed attempts
736–741 concern the explicit identity-map equality needed when extracting the
projection; all are retained in the [evidence](data/prolog-observed-triple-query-20261106.json).
Component entry coverage and ground receipts still need binding to these child
checks. Native assembly, export, controls and benchmark replay remain open.
No unified executable or certified frontier changed.

## Structural component entry interfaces (2026-11-06)

A selected-position row check derives finite-ground evidence from existing
transfer facts and observations. The component theorem uses a finite entry
table of predicate, arity and selected positions, with a child obligation for
each admitted entry. Unselected arguments remain unrestricted runtime terms.

Attempt 747 verifies the row theorem and entry-table composition. Attempts
743–746 are retained, including interrupted automated proof search and the
explicit runtime-type/pair reconstruction fixes.
[Evidence](data/prolog-structural-entries-20261106.json) records the exact scope.
Executable row-to-entry coverage and child-certificate binding remain open,
as do native assembly, export, controls and benchmark replay. No certified
frontier or unified executable changed.

## Structural coverage and PiDP child binding (2026-11-06)

The structural component bridge now checks an entry slot and transfer evidence
for every row. Receipt length, slot bounds, target predicate/arity and selected
finite-ground positions are mandatory. The child binding requires exact erased
component triples, retained success clauses and a shared PiDP check for every
entry. Its soundness theorem discharges the stable observed component relation.

Attempt 758 passes both theories and dependency audits.
[Evidence](data/prolog-structural-child-20261106.json) retains attempts 748–758,
including the interrupted automated proof and explicit type/index fixes.
Native synthesis, mixed-backend assembly, unified export, semantic mutations
and strict benchmark replay remain open. No certified gain or changed unified
executable is claimed.

## Checked structural/numeric source composition (2026-11-06)

A backend selector checks structural components through the shared PiDP bridge
and numeric components through the existing projected ITS checker. Finite
routing filters each component's exact same-rank row list and requires one
accepted child per rank; cross-rank descent remains checked. The source
constructor combines this table with relational Split assembly and transfer
contracts, and now has a verified source-root termination theorem.

Attempts 760–762 pass verification and dependency audits; attempt 759's missing
concrete label type is retained in the [evidence](data/prolog-stable-mixed-graph-20261106.json).
This supports separate structural and numeric SCCs, not inseparable mixed
recursion. Native synthesis, scheduler integration, XML/profile binding, export,
controls and strict benchmark replay remain open. No benchmark gain or unified
executable change is claimed.

## Mixed source profile and XML building blocks (2026-11-06)

The mixed constructor is instantiated with the same fixed source arithmetic
profile. XML building blocks retain existing component headers and parse new
relational ground-return Splits with both descent receipts. Structural backend
decoding checks the encoded child triples, success program and query metadata;
numeric decoding checks transfer identity, projections and the projected subject.
Only the verified backend checker can establish termination.

Attempts 764 and 768 validate these definitions and the profile theorem.
[Evidence](data/prolog-mixed-xml-development-20261106.json) retains parser/type/name
failures 763 and 765–767. Root XML assembly, export, native integration, mutation
controls and benchmark replay remain open. No unified executable or frontier
changed.

## Unified mixed source constructor (2026-11-06)

The verified root XML constructor binds the original source/profile, transfer
program, relational component graph, observed rows, rank routing and all backend
children. A verified list-erasure code equation permits executable generation
without equality on function-valued backend evidence. Generated checking logic
was not edited. Attempts 769–776 retain the XML/export development failures and
successful verification; generated Haskell typechecking passes in attempt 777.

Unified build 778 completes with executable SHA-256
`f52287d5a0e4d1028d9901743cb51cf00897e2a07e398268fbab2d813ca258f6`.
The numeric compatibility wrapper passes twice, and seven missing-obligation
mutations are rejected twice (779). All 69 retained Prolog and 93 LP-with-cut
certificates pass twice with this executable (780). This is retained-certificate
rechecking, not fresh native strict replay. The controls exercise the numeric
compatibility path, not structural children or relational Split returns.

[Pinned integration evidence](data/prolog-stable-mixed-integration-20261106.json)
records hashes, logs and the remaining gates. Native shared helper-model
assembly, continuation relation transport, independently scheduled mixed
children, broader semantic controls and strict benchmark replay remain open.
The frontier remains 61 YES + 8 NO; no new benchmark gain or superiority is
claimed. Protected-category production promotion remains gated.

## Probe-aware mixed helper returns (2026-11-06)

An open return model asserts the checked relation for selected predicates and
makes no claim for other ordinary predicates. The program-lifting theorem
connects this model to the existing actual-answer semantics. Successful probe
returns require an explicit success clause; this models returned substitutions
without asserting that the probed computation terminates. Helper termination
remains an independently checked graph/backend obligation. The new ground
receipt checks clause safety, user heads, source coverage, builtin coverage,
transfer, ground modes and the actual helper prefix. The mixed Split checker
accepts either the previous receipt or this proved extension.

Verification 804 and export 805 pass with dependency audits. The existential
head condition initially failed executable generation; an equivalent constructor
test fixes it without changing the logical condition. No generated checker code
was edited. Unified build 806 has SHA-256
`942d356409ade97f18d56e9a275909c49367e378a6895d8b85c2417ea439a07f`.

Fresh native and strict runs 1095 certify `prolog_mixed/primes.pl`, a renamed
changed-constant regression and the copied-list regression. Each run has two
checks by this executable, original-source audits and authorized reconstruction
receipts. Eleven advice/semantic controls pass, including divergent negated
helpers and divergent later answers. Certificate controls 810 pass 22 checks.
Attempt 807 showed that removing an optional type list is valid weakening; the
corrected control removes the required continuation input instead. Shared native
LP tests pass 562 tests with 10 ignored. All 69 retained Prolog and 93 LP-with-cut
certificates pass twice (808); this rechecking is not fresh full-frontier replay.

[Pinned evidence](data/prolog-probe-return-integration-20261106.json) includes
failed attempts and corrected harnesses. The 151-root remaining-gap experiment,
full-frontier guidance replay, superiority comparison and protected-category
production promotion are still pending at this checkpoint.

## Selective numeric observations, 2026-11-06

The stable numeric condition checker admits an explicit ignored-observation
receipt whose numeric consequence is only `0 = 0`. The original source
observation, row, endpoints, bindings, source operations and dependencies remain
checked. The receipt supplies neither integer typing nor any nontrivial numeric
fact. This lets an arithmetic backend retain supported constraints instead of
forcing the whole component through structural erasure.

Verification 813 reloads the affected theory and its dependents from the current
verified heap 804; export 814 and unified `make ceta` build 815 pass. Attempt 812
used an older heap with incompatible cached upstream context theories and is
retained as a failed attempt. Generated Haskell was not edited.

The same checker accepts three native/strict positives, including the real
`svcomp-twisted-c.pl` root and a renamed modulus-3 fixture, with 11 semantic/advice
controls and 20 certificate mutation checks. All 74 previously retained Prolog
and 93 LP-with-cut certificates pass twice (334 checks). Cut retention is
certificate rechecking, not a fresh protected-category production replay.
Unified checker SHA-256:
`d111fb4b857ddd04619aa237c84f9facab52b73f72e60232d134ef55376ccf91`.
[Pinned verification, export and integration evidence](data/prolog-selective-numeric-20261106.json).

## Checked comparison failure on ordered Prolog alternatives (2026-11-06)

The existing finite and stable comparison semantics now prove that a failed
comparison justifies its complementary comparison with reversed operands.
The evaluation comparison checker accepts either its legacy failure link or
a link checked with that additional observation. Stable source soundness
uses the actual failure outcome, preserving scalar behavior and uncaught
errors. No integer type follows merely from groundness or comparison failure.
Other source primitives and return-contract checkers remain shared.

Verification 827 checks the full mixed source XML dependency graph without
admissions. Export 828 regenerates `Prolog_Stable_Mixed_Generated.hs`, SHA-256
`08e830569a46e89e871066ed50963e6a9e92b5f5961fb47bfa63fc758135d331`.
Unified build 829, LP unit `ceta-lp-1.0-8c01b3149dc9e04d`, has checker SHA-256
`15bc36b5dc974a7f2871c28e87735e25d093a009dafe122c92b378bc4c0d5a20`.
Only verified exported code was installed; generated logic was not edited.

`svcomp-java-break-c.pl` and a renamed bound-7 fixture pass native search and
fresh strict replay, with source audits, two checks and complete authorized
receipts. All 13 semantic/advice controls and 24 certificate checks pass,
including removed failure branches, missing complementary observations,
incorrect strict complements, stale backtracking facts and floating counter
stagnation. Retention 830 rechecks all previous 67 YES + 8 NO Prolog proofs and
84 YES + 9 NO LP-with-cut proofs twice using this same checker: 336 checks pass.
This retention gate is certificate checking, not fresh protected-category
native replay or production promotion.

[The pinned evidence](data/prolog-comparison-failure-20261106.json) includes
failed verification attempts, the successful formal export, native/strict
receipts, rejection controls and retention logs. Ferrum's full-population replay
and final frontier are recorded separately in its state-of-the-art report.

## Checked successful truncating quotients (2026-11-07)

The stable arithmetic profile now fixes successful `//` evaluation to integer
truncation towards zero. Floating operands and zero divisors return no arithmetic
value. A checked positive-constant-divisor receipt preserves the exact quotient
relation between evaluated numerator and result bounds, with separate sign cases.
It does not assert that an unevaluated ground argument is an integer literal.
The existing source graph, contexts, return contracts, routing and independently
checked children remain required. Previous condition receipts remain replayable.

Verification 843 passes the operation, quotient and path lemmas without admissions;
export 844 checks the complete mixed source XML graph and regenerates its Haskell
module. Generated checking logic was not edited. Unified build 845 has SHA-256
`7b31687d90ff0b5a9394d076283dd26346d2b9f4b401657301b3272fe892da4a`,
LP unit `ceta-lp-1.0-870fce68d486fb09`. Other category export archives are unchanged.

Fresh native and strict runs certify `svcomp-java-log-built-in-c.pl`, a renamed
divisor-3 fixture and a compound-input divisor-4 fixture, each with original-source
audits, two checks by this executable and authorized reconstruction receipts.
Fourteen advice/semantic controls and 34 certificate checks pass. Formal controls
also establish negative truncation and rejection of zero/floating operands.
Source-level error fixtures remain UNKNOWN; these operation lemmas alone do not
certify their source graphs.

Retention 847 accepts all previous 77 Prolog and 93 LP-with-cut certificates twice
(340 checks). This is retained-certificate checking, not fresh protected-category
replay or production promotion. Ferrum records the complete 221-root replay
separately. [Pinned verification and integration evidence](data/prolog-quotient-integration-20261107.json)
retains unsuccessful verification attempts, successful export, controls and logs.

## Checked guarded variable-divisor descent (2026-11-07)

A new row-local receipt combines successful `//` evaluation with the actual
path comparisons establishing a divisor greater than one and a positive
numerator. It checks either a direct positive-numerator comparison or the
numerator's order relative to the divisor. Successful evaluation supplies
integer evaluated operands, even when their source terms are compound
expressions. The resulting numeric relation requires a nonnegative quotient
strictly smaller than the evaluated numerator. No integer-literal assumption
or success fact is exported to an unrelated or resumed alternative.

Verification 850 proves the operation/domain and descent lemmas; 852 checks the
receipt and complete stable path bridge without admissions. The checker binds
the ambient observations to the same source row. Export 853 verifies the full
mixed source XML graph and regenerates the module; no generated checking logic
was edited. Unified build 854 has SHA-256
`9a372491186a4162f3252397d4c516abaae6f96974891703a8660d55ae565c18`,
LP unit `ceta-lp-1.0-13ec7c525a52aeac`. Other category export archives are unchanged.

Native and strict runs certify `log-recursive-c-true.pl`, a renamed returned-count
fixture and a compound-input fixture. The source proof retains the existing
Split, actual successful-return contract, helper dependency and continuation
interface. All 15 advice/semantic controls and 42 certificate checks pass,
including missing guards, strictness, initialization, return interfaces,
helper/continuation dependencies, stale alternative facts and a divergent
floating helper before a quotient. Each positive has original-source audits,
two checks by this executable and authorized complete reconstruction receipts.

Retention 855 rechecks all previous 78 Prolog and 93 LP-with-cut certificates
twice (342 checks). Ferrum's complete 221-root strict replay 1266 establishes
71 YES + 8 NO separately. This is not protected-category production promotion.
[Pinned evidence](data/prolog-quotient-descent-20261107.json) preserves verification
attempts, the export/build, controls, retention and the corrected metadata-count
assertion in pinning attempt 856.

## Checked bounds from quotient comparisons (2026-11-07)

Successful comparisons against unevaluated quotient expressions now retain
checked numeric consequences. A positive literal divisor gives the exact
truncating quotient relation. For a general divisor, a checked integer counter
is bounded above by the absolute evaluated numerator. Successful comparison and
quotient evaluation supply the required operand domains; no integer-literal or
positive-divisor assumption is imposed on arbitrary ground arguments. Both
numerator signs remain covered. Existing graph, branch, Split, actual-return
and child-dependency checks are unchanged.

Verification/export 865 checks the new lemmas and complete source XML bridge,
then generates the mixed checker module without manually editing generated
logic. Unified build 866 has SHA-256
`72cb706bb4ebb85dda6abc2e58cbd0a915ded079394a220452720f4d3471b7b7`,
LP unit `ceta-lp-1.0-2435cf522099b6fc`. Only the LP export archive changed.
Unsuccessful proof-development attempts 857/858/860–864 are retained alongside
the successful checks and export.

The original `Euler_queensu-cs260/prime.pl` and three renamed/generalized fixtures
pass fresh native and strict replay, with original-source audits, two checks by
this unified executable and authorized reconstruction receipts. One fixture
retains a recursive helper's returned count through its relational Split.
All 14 advice/semantic controls and 54 certificate checks pass, covering missing
observations, type facts, alternatives, bindings, routing, helper/continuation
interfaces and children. Changing bounds, floating counter stagnation and later
divergence do not acquire source proofs.

Retention 867 accepts all previous 79 Prolog and all 84 YES + 9 NO LP-with-cut
certificates twice (344 checks). Ferrum's complete 221-root strict replay 1288
reaches 72 YES + 8 NO with no lost verdict. Retention is certificate rechecking,
not fresh protected-category native replay or production promotion.
[Pinned verification and integration evidence](data/prolog-quotient-bounds-20261107.json)
includes every attempt and the unchanged other-category archive identities.

## Checked positive-divisor modulo descent (2026-11-07)

The established source graph now supports a checked modulo descent receipt.
Actual successful evaluation of `A mod B`, together with the same path's
comparison `B > 0`, yields a nonnegative remainder strictly below the evaluated
divisor. Successful modulo evaluation establishes integer evaluated operands;
groundness alone does not establish that domain. The source profile retains
floor-modulo signs, zero-divisor errors and floating-operand errors. Existing
contexts, failure alternatives, Split actual-return contracts and separately
checked child dependencies remain required.

Verification 869 proves the operation, progress, condition and path lemmas
without admissions. Full source XML export 870 passes and regenerates the mixed
module. Unified build 871 has SHA-256
`c462141ca375232aaefc2ddb901d42f565aadd81354536a2154392142d743821`,
LP unit `ceta-lp-1.0-f194b9292ec4a487`. Only the LP export archive changed;
generated checking logic was not manually edited.

Three original GCD benchmarks and two generalized fixtures pass native and
strict replay, including a helper's returned result across a Split. All 15
advice/semantic controls and 44 certificate checks pass. Mutations cover the
modulo operands, actual positive guard, bounds, initialization, alternatives,
routing, return interfaces, helper/continuation dependencies and child proofs.
Divergent negative-divisor, later-answer, stale-guard and floating-helper controls
remain unproved. Two initially misnamed finite negative-divisor fixtures were
corrected before strict validation; original attempts and corrected controls
are retained in Ferrum's family audit.

Retention 872 accepts all previous 80 Prolog and 84 YES + 9 NO LP-with-cut
certificates twice (346 checks). Two legacy quotient fixtures strictly replay
with their previous guidance and this checker. Full 221-root replay is recorded
separately by Ferrum. This retention check is not fresh protected-category native
replay or production promotion.
[Pinned verification and integration evidence](data/prolog-modulo-20261107.json)
binds the export, checker, controls and retention checks.

## Conditional actual helper returns (2026-11-10)

Logic/export commit `5b7ecf0` extends the shared answer-sensitive semantics with
checked library delegation and conditional control, then proves complete logical
path coverage and actual-successful-return contracts across established Prolog
Splits. Return contracts remain separate from helper termination. Failed condition
bindings do not enter the else path. Finite groundness requires checked input or
return premises; cyclic equations alone cannot provide a structural measure.
The existing dedicated conjunction, equality and truth symbols are preserved.

Full mixed-source XML verification 1047 and export 1048 pass, including eight
executable source-cover regressions and dependency audits. The regenerated
mixed module has SHA-256
`8dcc37019d5b664801199b8cab21e5075200c49ca11aae9a2ac4457223bc3693`.
Unified `make ceta` build 1049, LP unit `ceta-lp-1.0-b10cf37d6904b875`, has SHA-256
`98ceb8a60719e1eb3ebd7c70f80ba1b965b30e7f9dff1d2f2013b9ce00a600ea`.
No generated checking logic was manually edited; other category exports remain
unchanged. Earlier rejected assemblies and proof-development attempts are retained.

Ferrum `ba973cd3` strictly replays the fixed 221-root population to 79 YES + 8 NO,
adding both Hett grouping roots and preserving every previous result. All 87
results have source audits, two checks with this executable and independently
authorized complete receipts. The three-positive family passes native and strict
replay, seven semantic/advice controls and 40 certificate mutation checks.
Retention 1050 passes 356 checks across all previous 85 Prolog and 93 LP-with-cut
certificates. This is not protected-category production promotion.
[The pinned cross-repository evidence](../../ferrum-prolog-release/docs/data/prolog-control-returns-20261110.json)
includes the archive, hashes, failed attempts, full replay and remaining gaps.

## General control-return shape integration in progress

Verification 1056 proves that actual conditional helper returns preserve seed
shape facts under substitution and satisfy the existing shared shape-transfer
checker. Verification 1057 checks the executable control-shape receipt and its
returned context; 1058 checks its Split interface and descent composition.
Full mixed-source XML verification 1059 passes with the additive
`LPPSControlShape` component and `relationalShapeSplit` parser. Existing component
forms remain available. These changes have not been exported or promoted.

Verification 1061 extends the receipt with conditional integer-return facts from
that same actual helper model. Full mixed-source XML verification 1062 passes.
The native connection now discovers shared shape grammars, emits the new Split
component and exposes residuals through an additive explicit strategy. Preparation
1474 passes for a conditional helper returning a list with open record fields and
its renamed variant; native shared LP tests 1477 pass 587 tests with thirteen
ignored. Export 1063 is in progress. These checks do not establish a new certified
benchmark result; the baseline remains 79 YES + 8 NO. Unified executable checks,
semantic mutations, strict replay and benchmark gains remain outstanding.
Verification failures 1053–1055 and 1060 and all successful attempts are retained
under the persistent target directory.

Export 1063 and unified build 1068 are complete. Checker SHA-256 is
`751a5fb6e3ee7c6b42c46dc54bbb4089c36643489d93d63c58c7b9d4c1dd883c`.
Retention 1073 accepts all 87 Prolog and 93 LP-with-cut certificates twice (360
checks). Ferrum family 1490 passes four native and four strict positives, seven
semantic/advice controls, and mutation 1493 passes twelve checks. Full strict
replay 1492 retains 79 YES + 8 NO and all source hashes; all 87 receipts are
independently authorized. No new benchmark gain or production promotion follows.
[The cross-repository evidence](../../ferrum-prolog-release/docs/data/prolog-control-shapes-20261110.json)
retains failed attempts, including the corrected native ground-observation/guard
slot mismatch, successful source certificates and checking identities.

Separate projection foundations pass verification 1087: inductive return shapes
justify finite selected projections, and the existing PiDP proof discharges a
component when every actual entry has such a projection. Verification 1076
rejects keeping or collapsing onto unconstrained fields and permits an erased
arbitrary head. These theories are not connected to the exported backend parser
yet. The next integration must retain every row's observations, bind the selected
filter to its shape coverage and expose any filter restrictions in complete
residual identities. Whole-value groundness must not replace that obligation.

## Established Prolog finite return projections

Commit `f2c43b0` connects the verified finite-shape component theorem to the
existing structural backend. The optional `shapeStructuralBackend` envelope
checks every observed entry, its actual-return seeds, the argument filter and
all PiDP children. A retained unconstrained shape edge is rejected; cyclic or
open erased fields cannot become a decreasing measure. The original structural
backend remains accepted.

Verification 1088/1089 and export 1090 pass. Unified O2 integration is
`target/unified-shape-backend-1091/ceta`, SHA-256
`a1a1ec337905d56cf13fcbbd6cf5f3c796bcee46d85b2a2054080313ce563c4d`,
on `codex/prolog-production-integration`. Ferrum `7e989ea2` passes four native
and four strict family proofs, seven controls and 24 mutation checks. Retention
1092 passes 360 checks over 87 Prolog and 93 LP-with-cut certificates. Complete
Prolog strict replay 1508 preserves 79 YES + 8 NO / 221 with no new benchmark
verdicts. This is a development integration, not protected-category production
promotion. Evidence is pinned in the sibling Ferrum checkout at
`docs/data/prolog-shape-backend-20261111.json`.

## Shared Prolog disjunction and actual returns, 2026-11-11

Commit `05de7d7` extends the shared Prolog answer stack with checked static
disjunction. Both alternatives retain their incoming environment. Scope,
reinterface and nested-Split composition proofs cover the additional transition;
conditional choice retains its existing rule. Complete path extraction connects
actual successful returns to the existing control-aware contracts. Unsupported
dynamic or cut-containing alternative lowering remains an explicit obligation.

Verification 1106/1107 and full verification/export 1108 pass. The Isabelle
exported mixed module has SHA-256
`7f2799abab668e28fc60c5188c062684444ff9632c9f3973c4d489b1ae4e41b0`;
shared generated helpers are unchanged. Unified `make ceta` integration is
`target/unified-prolog-choice-1109/ceta`, SHA-256
`6da699e60e25462f7457a9ff14ae3a75b5f7f4995624ba74e13a90b542a8f9dc`.
No generated checking logic was edited by hand.

Ferrum `c8a76f65` passes two native and two strict generalized fixtures, ten
controls and 34 mutation checks. Retention 1110 preserves 87 Prolog and 93
LP-with-cut certificates on 360 checks. Full strict replay 1536 preserves
79 YES + 8 NO across all 221 Prolog roots, with unchanged source hashes and all
87 receipts authorized. Shared tests pass 595 tests with thirteen ignored.
There are no new benchmark gains and no protected-category production promotion.

[Cross-repository evidence](../../ferrum-prolog-release/docs/data/prolog-choice-returns-20261111.json)
records all attempts, the generated export, complete receipts and the fresh
16-root cohort. All sixteen targets remain UNKNOWN; the next shared source
interface work concerns builtin/library return relations. Fixture certification
does not establish benchmark gains or superiority.

## Nonnegative builtin-result contexts (2026-11-11)

`LP_Prolog_Natural_Return_Context` and
`LP_Prolog_Stable_Natural_Return_Context` introduce integer and nonnegative
observations from a proved integer-valued result. The latter requires the
existing integer-compatibility premise of the binary64-aware source profile.
`LP_Prolog_Finite_Context_Length` and `LP_Prolog_Stable_Length` instantiate these
rules only for the fresh scalar before output unification. Freshness covers the
source stack, saved environments, context, interface, free variables and guards.
The unchanged link checker must justify every transported child fact.

Verification 1113 passes the integer-only adapter; 1116 passes the stronger
nonnegative adapter and both reusable context rules. Failed attempts 1114 and
1115 retain their logs (reserved proof identifier and missing integer-value
proof simplification). Full source-assembly verification/export 1117 passes.
CeTA commit `964e3a9` is integrated through the `prolog_natural_result_integration`
metadata in `scripts/unified-exports.json`; only the generated mixed source
module changes. Unified build 1118 has SHA-256
`a3c5c25f2f14e6b7d57500673ff212be5e1787b8a58bf175502af2bf878579e9`.

Ferrum `bcfe16b4` passes three native and three strict fixture certificates,
fourteen controls and twenty-four mutation checks. Retention 1119 preserves all
87 Prolog and 93 LP-with-cut certificates with 360 checks. Full strict replay
1555 preserves 79 YES + 8 NO / 221 and all complete receipts. The remaining-gap
native diagnostic has no complete benchmark proofs. No benchmark gain or
production promotion is asserted. Pinned cross-repository evidence is
`../ferrum-prolog-release/docs/data/prolog-natural-results-20261111.json`.

## Stopped answer contracts for nested undefined calls (development, 2026-11-11)

`LP_Answer_Stop_Contracts` adds a shared contract adapter for source-justified
uncaught errors. It proves termination lifting, preservation of actual successful
answers, absence of answers on an error exit, retention of unstopped loops,
primitive composition, continuation attachment and ordered suffix reflection.
The adapter clears the complete annotated stack; it does not resume a saved
alternative with stale facts. Its stop predicate is a separate checked premise.

`LP_Prolog_Stopped_Answers` instantiates that premise with the existing
`lpp_undefined` and builtin-dispatch conditions and proves simulation into
`lp_prolog_source`. Unsupported builtin-domain self-loops are retained.
`LP_Prolog_Undefined_Frame` checks definition absence against the complete source
program and exact predicate arity, excluding builtins. Its tests cover defined
predicates, differing arities and saved alternatives.

Primitive actions reuse the existing context/link checker. Stopped modular
contracts reuse the shared ordered-stack composition rules. Arithmetic-result
normalization uses the existing scalar evaluation and rational equality rules.
The original observed-is theorem now factors through a continuation-parametric
context theorem, shared by its old contract and the stopped contract; freshness,
integer compatibility, context facts and saved environments are unchanged.

Verification 1136 passes the shared stop, source simulation, primitive and
undefined-frame rules; 1137 passes stopped evaluation normalization. Verification
1141 passes the context refactor and the original contract; 1142 passes stopped
stack composition. Full combined source verification 1143 passes, including the existing mixed XML source assembly. Verification 1145 passes the analogous continuation-parametric constant-result theorem and both its ordinary and stopped contracts. Earlier
failed and interrupted attempts 1122–1140 retain their logs. No checker export,
unified executable change, new root certificate or benchmark gain is claimed.

Ferrum inventory 1591 reproduces the undefined-operation rejection on the
established graphs for two original sources, with hashes checked against the
221-root replay. One has no Splits, the other has nested Splits. The next required
step is checked source module/graph assembly, then native receipt emission and
source-audited twice-checked strict replay. The existing 79 YES + 8 NO frontier
and production gate remain unchanged.

The saved-alternative fixture exposes a separate precision obligation: the graph
retains the later divergent clause even when an earlier clause necessarily aborts.
A no-answer summary cannot justify eliminating that clause, because ordinary
finite failure also has no successful answers and resumes alternatives. Safe
suffix discharge needs a checked abort effect or continuation-unreachability
contract. The fixture remains an unresolved positive control; its defined-failure,
divergent-prefix, builtin-repeat and rational-callable variants remain negative
controls. Inventory 1593 records their current established graphs and first gaps.

Development module composition keeps the existing action witnesses and contexts.
Its stopped dispatcher distinguishes checked undefined exits from ordinary actions.
Length and subtraction compositions remain rejected until their stopped contracts
are connected. No acceptance change to the existing exported checker is made.

Verification 1154 passes stopped module dispatch, scope restoration and ranked
control-graph composition. These are conditional contracts: each boundary still
requires its complete child contract. The action witness type wraps existing
actions or a source-checked undefined exit; no benchmark name appears in a rule.
Attempt 1146 and 1148 exposed theorem-instantiation errors, 1147 used a nonexistent
heap path, 1149 exposed a dispatch instantiation error, 1152 was explicitly
interrupted during broad simplification, and 1153 exposed missing stack-emptiness
preservation under scope renaming. The corrected proof uses explicit scope
induction and verifies preservation of stack length and emptiness. All attempts
are retained. Combined verification 1155 passes the original mixed XML assembly
after the constant-result refactor. The checked implementation is commit
`f06aa82` on `codex/prolog-production-integration` in this CeTA tree.
Pinned evidence is `../ferrum-prolog-release/docs/data/prolog-stopped-contracts-20261111.json`.

### Stopped graph source assembly and certified integration

Verification 1168 connects the stopped contracts through return-interface
projection, source-instance boundaries, ranked regions, actual-return Split
composition, and complete referenced module graphs. Ground and shape receipts
reuse their existing successful-return theorems through the checked inclusion
of stopped actual answers into ordinary actual answers. The shared region-descent
rule now takes an explicit boundary predicate; the legacy checker and theorem
retain their previous behavior.

`prologEstablishedStoppedSEGMixedProof` binds the same source profile, complete
program, query, transfer model, initial contexts, module roots, observed triples,
routing and structural/numeric backend proofs. Region headers must match the
parent program, fuel, transfer model and root index. Stopped actions preserve the
existing region record and bind its action projection; checked undefined exits
are distinct from unresolved module boundaries. The graph theorem concludes
termination of the existing `lp_prolog_source`, without assuming every abstract
helper output is an actual return.

The new native scalar strategy uses the established graph with historical
construction and independently scheduled backend choices. Old strategy atoms
retain their previous preparation. Native tests 1597 pass 602 with thirteen
ignored, including undefined-call arity, builtin, rational-callable and recursive
obligation controls. Export 1169 passes, with generated mixed-module SHA-256
`c3213dbc3ecad2423f419452c35ae19f55a7ecab61d679dd963368fb7db36960`.
It exports both old and stopped source checkers in the same generated module.
Unified build 1170 passes, with executable SHA-256
`2305139e31b74080cdae3c470bae3fd737bea79d73e520e2df1d5132629033c1`.
Retention 1172 passes 360 checks over 87 Prolog and 93 LP-with-cut certificates.
Ferrum's complete strict replay 1603 establishes 80 YES and eight NO on the same
221 sources, preserving every previous verdict; all 88 receipts are independently
authorized. The gain is the original `AProVE_numeric/svcomp-ex3b-c.pl` source.
The other candidate, `Hett/p2_10.pl`, reaches a missing comparison groundness or
return-fact obligation, without reaching residual search.

Family 1600 passes three native and three strict fixtures, including copied-list
helper returns, with fifteen controls. Mutation 1602 passes fifteen cases twice;
Split mutation 1605 passes twenty-three cases twice, including two individual
dependency-removal audits. Attempt 1604 incorrectly expected every model
declaration to be necessary: an unused equality declaration may be removed.
Required return dependencies and complete module coverage remain checked.
Preparation 1601 stopped before root execution because an equality-only guidance
merge did not recognize an already-authorized strategy alternative. Replay 1603
retains that old alternative and independently authorizes the observed action.
These attempts are preserved; no checker acceptance rule was weakened.

Stopped length and subtraction local actions and abort-based suffix discharge
remain explicit gaps. Production promotion remains gated on protected-category
replay with this same unified executable.


## Prolog observed-equation normalization and incremental builds

Verification/export 1214 adds checked equation enrichment between the original
stopped SEG obligations and independently scheduled component backends. Original
source rows, helper prefixes, endpoints and complete row coverage remain bound;
normalization adds consequences of initialized equations without integer-domain
or finite-spine assumptions. Optional normalization fields default to the old
row subject for existing artifacts. Unified build 1211 has SHA-256
`8971c7405a3e13890cb2a070edb4568501c8534f80dff5bc178ca8cf477ff71b`.
Six fixture native/strict replays, fourteen controls, eleven mutation cases twice
and 362 prior Prolog/LP-with-cut certificate checks pass with this checker.
Benchmark gains and production promotion are not established by those fixtures.

Use `make ceta CETA_REUSE_BUILD=target/unified-prolog-normalization-reuse-1215`
with a fresh output/install directory for subsequent Prolog exports. The builder
hash-checks and reuses unchanged category libraries read-only, including libraries
referenced transitively by prior builds. Only changed identities rebuild.
Validation 1215 and 1216 reuse all eight libraries and produce the identical
binary hash; no category library is recompiled. Their logs and build manifests
are under `target/prolog-normalization-reuse-1215.log`,
`target/prolog-normalization-reuse-1216.log` and the corresponding unified build
directories. Reusing these libraries preserves immutable previous checkers.


## Checked Prolog helper cases and context-groundness at Split boundaries

The current integration atop `f617aaa` on `codex/prolog-production-integration`
checks exhaustive successful-helper clause cases and transports initialized
integer-return observations through finite, stable and stopped Split boundaries.
Boundary groundness may be derived from the checked incoming evaluation context;
this is proved by the context-groundness lemma, not assumed from a terminating
helper. Existing boundary checks remain accepted. Saved alternatives and module
dependencies retain their original obligations.

Verification 1321 and 1322, export 1323, installation 1324 and unified build 1325
are preserved under `target/prolog-context-*` and
`target/unified-prolog-context-boundary-1325`. The immutable executable has
SHA-256 `8fac3b39e6c30bc810cb2e566dbc4141691ec04f37f0e48ccc6231e4c0cace64`.
Seven unchanged category libraries were reused; no generated checking logic was
patched. Retention 1326 checks all 91 retained Prolog and 93 LP-with-cut
certificates twice (368 checks).

Ferrum strict replay 1831 preserves 81 YES and ten NO on the fixed 221 sources,
with 91 independently authorized complete receipts. Family 1835 passes five
native and five strict fixtures plus thirteen controls. Helper-case/context
mutation suite 1833 passes sixteen cases twice; ground-comparison suite 1834
passes eleven cases twice. Compound arithmetic input is a positive case when
its actual evaluation returns an integer; an earlier negative expectation was
corrected. There is no new benchmark gain from the boundary extension itself.
Protected-category production promotion remains gated.

## Binary64 arithmetic in checked Prolog source loops

Integration `31e6eef` on `codex/prolog-production-integration` extends the fixed
stable scalar-operation profile with integer and binary64 arithmetic, preserving
separate operand conversion, signed zero, finite range and exact scalar
comparisons. Isabelle theories prove expression evaluation and source steps,
then instantiate the shared complete-stack source-loop checker. Sixteen
executable rounding controls supplement these proofs. Generated Haskell logic
was not edited. The retained pumping interface still requires its original
barrier and dependency conditions; unsupported pending-alternative pumps are
not accepted.

The resident verification transcript is
`target/prolog-binary64-resident-1330.log`; failed attempts remain there.
Fresh export `target/prolog-binary64-export-1331` and installation 1332 bind the
new function alongside all existing stable, stopped and ground-integer checks.
The initial export driver name collided with a loaded theory and produced no
module; a unique fresh theory generated the verified export. The reusable
export script now gives output directories distinct theory names.

Unified build 1333 reuses seven libraries and rebuilds only LP. The installed
checker `target/installed-prolog-binary64-1333/ceta` has SHA-256
`3486eda4f44017e0e67ee136c2d0a49050e7e8c91a5aaed0a501a7fe3ff8366d`.
Retention 1334 passes all 368 checks of the prior 91 Prolog and 93 LP-with-cut
certificates. Ferrum integration `186493f5` strictly replays all 221 original
sources in frontier 1858: 81 YES, seventeen NO, 123 UNKNOWN, and 98 independently
authorized complete receipts. Seven new NO roots use this binary64 route.
Family 1854 passes eight native and eight strict proofs plus thirteen controls;
mutation suite 1856 passes 36 checks with this same executable. Twelve saved
native cycle candidates remain source-parent assembly obligations. This is not
a matched-semantics superiority claim or protected-category production promotion.

## Shared pending-stack pumping for checked builtin traces

Integration `da399c2` on `codex/prolog-production-integration` generalizes the
existing LP-with-cut pending-stack argument through a shared execution contract
and proves its Prolog builtin instance. Recorded loop states must be nonempty
and have no selected cut when arbitrary suffixes are pumped. Error transitions
that discard the stack are excluded. Existing barrier-only proofs remain valid.
The ground-integer and binary64 source checkers instantiate the same theorem;
there is no replacement operational semantics or SEG.

Resident verification 1335 preserves two proof-automation failures followed by
the successful shared, source-step and complete-trace proofs. Fresh export 1336,
installation 1337 and unified build 1338 produce checker SHA-256
`dc23ddc547070e38b72978fb0ce0681fa03b0306ecd48959c393828f7782673a`.
Only the LP library rebuilt; seven category libraries were reused. The verified
export and original helper modules are installed without hand-edited generated
logic. Retention 1339 passes 382 checks over the prior 98 Prolog and 93 LP-with-cut
certificates.

Ferrum integration `cfb76576` reuses the existing checked resolution transposition
earlier in a trace and re-executes subsequent operations exactly. Native
constructor capabilities preserve the oldest integer route's barrier restriction.
The final strict 221-root replay 1871 certifies 81 YES and 29 NO with 110 complete
receipts independently authorized: twelve new NO roots and no lost verdicts.
All nineteen saved binary64 candidates are now certified. Shared tests pass 636
cases; four fixture suites pass fifteen native and fifteen strict proofs, and
mutation suites pass 64 checks. A byte-identical pending-stack certificate is
rejected by the previous checker and accepted twice by checker 1338, as recorded
in Ferrum's `target/prolog-pending-previous-checker-1861/new-checker-comparison.json`.
The broader remaining-root scan finds no further gains. Protected-category
promotion and matched-semantics superiority remain separate gates.


## Checked positive arithmetic contexts for Prolog (2026-11-12)

Integration `219557c` in `/work/dfm/festschrift/CeTA-prolog-release`, branch
`codex/prolog-production-integration`, adds indexed consequence receipts for
positive literals, equations, exact positive quotients and positive integer lower
bounds. The stopped-region composition checks local enrichment and incoming
boundary obligations without resetting established contexts. Actual integer
membership is required for the lower bound; groundness is insufficient. Missing
exactness cannot justify quotient positivity (`1 // 2 = 0`). Theorems preserve
actual stable arithmetic semantics, including the source's binary64 behavior.

Fresh Isabelle export `target/prolog-positive-lower-export-1346` produces Haskell
SHA-256 `66cb656e559d706b08784fa244b383b1345a5cfc768865b849d24149ae435e54`.
Installation 1347 retains a complete matching source snapshot. Unified build 1348
reuses seven unchanged category libraries and rebuilds LP only. The executable
`target/installed-prolog-positive-lower-1348/ceta` has SHA-256
`bf5d58f2bf81d31b4309f6898283cdd66e7eb070f8a825c8f9a7cbba3f396b9b`.
No generated checking logic was patched. Retention 1349 passes 406 checks over
all 110 prior Prolog and 93 LP-with-cut certificates.

Ferrum integration `b599c6b4` and full strict replay
`../ferrum-prolog-release/target/prolog-positive-frontier-1915` establish
82 YES + 29 NO on the unchanged 221 sources, adding `Hett/p2_10.pl`. All 111
complete receipts are independently authorized, with two checks per result by
this same executable. Family 1911 passes three native and three strict proofs
with twelve controls; benchmark gate 1918 passes native/strict with eleven
controls. Mutation suite 1917 passes 38 checks across nineteen cases, including
missing arithmetic derivations, incorrect indices, missing module dependencies
and ground/integer confusion. LP-with-cut remains 84 YES + 9 NO.

Earlier checker 1343 passed retention but could not close the zero-loop numeric
abstraction; the final consequence and aligned-bound projection remove that
obstruction. Attempt 1916 retains the expected old-checker rejection of the new
constructor. Protected-category production promotion remains gated. The complete
[pinned Ferrum evidence](../../ferrum-prolog-release/docs/data/prolog-positive-context-progress-20261112.json)
records replay, source snapshots and executable identities.

## Prolog constructor backends and finite length returns (2026-11-12)

The established source checker now accepts the shared constructor dependency-triple
backend with checked finite-ground observations at every entry. Other arguments
may remain rational; a finite graph representation is never a structural measure.
Constructor proofs require ground coverage and cannot use shape-only coverage.
The exact triples, success program, filters and complete DP child remain checked.

The stopped-source composition now instantiates the existing finite-length
semantics, retaining fresh results, output unification and failure/error behavior.
Resolution links may derive groundness from checked context and unification
equations. New controls exclude cyclic equations without a finite ground seed.
The XML format can reference the unique enclosing success-transfer contract;
references expand before the existing parser and semantic checks. Distinct nested
contracts remain inline. No generated checking logic was patched.

Verified export 1357 and source-bound installation 1358 feed unified build 1359.
Only LP rebuilt; seven category libraries were reused. The checker SHA-256 is
`e7d072bca0d006fa7f9d7b0a8ec1c7deb920ae7e600c120e498201ebfec8eedd`.
Retention 1360 passes 408 checks of all 111 Prolog and 93 LP-with-cut certificates.
Ferrum family 1963 passes five native and five strict source proofs, including
two original benchmark gaps, with eleven negative/advice controls. Mutation suite
1964 passes 46 checks over 23 cases. Full strict Prolog replay 1970 establishes
84 YES + 29 NO on the unchanged 221-root population, preserving every prior verdict and authorizing all 113
complete receipts. Fresh LP-with-cut replay 1971 preserves 84 YES + 9 NO and
nineteen unguided inputs with the same binaries. Ferrum integration is `0437a30c`;
CeTA integration is `47943a7`. Protected-category promotion and superiority
remain open.
[Pinned integration evidence](../../ferrum-prolog-release/docs/data/prolog-constructor-progress-20261112.json)
records the source snapshots, executable identities and retained attempts.

## Evaluated integer values and staged observations (2026-11-15)

Integration `bfe0ef46fddc81afd77663ab3d70cc8a6ee43663` checks integer-valued
compound expressions from successful arithmetic observations and existing
literal-integer facts. It does not turn groundness into integer typing.
Floor-order receipts preserve scalar order, including binary64 values, while
staged argument expansions retain nested observed expressions with checked
arity and dependency coverage. The sequence theorem composes the existing
stable numeric and actual-return backends. Old backend formats remain valid.

Verified Isabelle export 1433, installation 1435 and unified build 1436 produce
checker SHA-256
`ff5fc747079fb8088e374ec7a71f8cd3e9c2a614dcf4532fc83381f64ad67537`.
Only LP rebuilt; seven category libraries were reused. An invalid Array mapping
in attempt 1429 was corrected in the final export driver's code-printing setup.
Generated checking logic was never patched. Verified heap 1437 is retained.

Ferrum `fb9a445a6654cd9c47593efd3f1723db1e4432b6` passes four native and four
strict fixtures, eleven controls, four packaged strict proofs, and fifty
mutation checks. Fresh complete replay 2227 preserves 84 YES + 48 NO on 221
Prolog roots and authorizes all 132 receipts. LP-with-cut replay 2228 preserves
84 YES + 9 NO and authorizes all 93 receipts with this same checker. This is
infrastructure and residual precision progress, with no new benchmark verdict.
Protected-category production promotion remains gated.
[Pinned Ferrum evidence](../../ferrum-prolog-release/docs/data/prolog-evaluated-integer-progress-20261115.json)
records source snapshots, executable identities and attempts.

## Positioned Prolog helper contracts and multi-scale retention, 2026-11-15

Implementation `18d850a996580ba1f60dee49f6c6a0757ad2b0bf` checks conditional
successful-return order contracts and magnitude evaluation observations in the
established Prolog source graph. Explicit observation positions preserve the
exact emitted child subject. Distinct `positionedRow` tags fix XML committed
choice, while legacy `row` proofs remain replayable. The full checked export
1475 is installed in `lp-source-stable-mixed.tar.gz` through the unified manifest;
no generated checker logic was patched.

The O2 unified build 1477 rebuilt LP in 540.1 seconds and reused seven unchanged
libraries. Its immutable executable
`target/installed-prolog-positioned-1477/ceta` has SHA-256
`031e9f4f70276aed4fa89f6518b4673ce1239bad9957306e7b09b1b65fa47771`.
Ferrum implementation `90b82f2781d7d320531081adaa09ad51b759dba2` strictly replays
84 YES + 52 NO on all 221 Prolog roots, retaining every prior verdict and adding
four binary64 NOs. LP-with-cut retains 84 YES + 9 NO with this same checker.
Three helper-return source fixtures and 20 NO cases pass native and strict
checks; 106 mutation checks and 19 merged-package fixture replays pass.

The [pinned cross-repository audit](../../ferrum-prolog-release/docs/data/prolog-order-multiscale-20261115.json)
records source identities, source audits, two same-checker passes, complete
receipts, environment, per-root timing and all unresolved roots. The
[authoritative Ferrum ledger](../../ferrum-prolog-release/docs/state-of-the-art.md)
records failed attempts and diagnosis. Production promotion remains gated on
the protected-category replay; this category integration does not claim that
release gate or a matched-semantics comparison with AProVE.

## Prolog finite arithmetic-expression shapes, 2026-11-15

CeTA commit `5c2e82167d6efe70cb83c668a39580c2ab49c93f` on
`codex/prolog-production-integration` checks total integer evaluation from
inductive finite return-shape grammars. Ground/arbitrary grammar children and
floating literals cannot establish the new fact. The existing source context,
initialization and Split checks remain required. Numeric observation selection
preserves the two legacy receipt formats. Isabelle export 1481 and its ten
positive/negative tests passed; unified build 1483 reused seven libraries and
rebuilt LP only. Generated checking logic was not patched.

The immutable unified executable is
`target/installed-prolog-arithmetic-shapes-1483/ceta`, SHA-256
`b7c67a3e012da0ab919cb261390a73801764762cf3b333c3e3aac9232971824f`.
Ferrum commit `fa1681501b49b4a6ad2a1d99fd3500b49af9e7c0` supplies native
shape discovery and fixes dependent equation-parameter completion. Fresh strict
replay certifies 85 YES + 52 NO on the fixed 221 Prolog roots, retaining all
previous verdicts, and preserves 84 YES + 9 NO for LP-with-cut using this same
checker. All retained results have source audits, two checker passes and
authorized reconstruction receipts. Three source-family proofs, 14 controls,
20 new mutation checks, 106 legacy mutation checks and 21 packaged fixture
replays pass. Production promotion remains a separate protected-category gate.

The [Ferrum pinned audit](../../ferrum-prolog-release/docs/data/prolog-arithmetic-shapes-20261115.json)
records both implementations, frozen source hashes, guidance and per-root
search/checking evidence. The source gain is Weinert `prime.pl`; recurring
abstract residuals found during diagnosis are not counted as source NOs.

## Prolog evaluated-input helper contracts, 2026-11-16

Integration `12b70142623856baaa43855b5f7d556c6c81f809` on
`codex/prolog-production-integration` preserves successful numeric comparisons
in the established helper model and checks actual-return value-domain and
conditional order summaries. The new component backend checks every selected
helper dependency and its observation position before composing the existing
numeric child proof. Groundness and comparisons alone do not imply integer
values. Legacy source strategies and proof formats remain valid.

Isabelle integration 1495 and export 1496 passed. The generated source is
installed through `scripts/unified-exports.json` and
`tests/unified/exports/lp-source-stable-mixed.tar.gz`; generated checking logic
was not patched. Export took 412.609 seconds. Unified build 1498 rebuilt LP in
510.8 seconds and reused seven unchanged libraries. Its checker SHA-256 is
`5a34aacae9e4838f767bec1f0fbf15cfa2f4d8580fbec93d6b4a0c9f27089430`.

Ferrum `3d3f077e9aba28fded49df368381026b354b1b68` certifies and strictly replays
86 YES + 52 NO on all 221 Prolog roots, preserving every prior verdict and
adding Euler `euler-03.pl`. All 138 results have original-source audits, two
checks and authorized reconstruction receipts. LP-with-cut retains 84 YES +
9 NO with this same checker. Three source-family proofs, thirteen controls,
28 new mutation checks, 106 legacy mutation checks and 23 packaged fixture
replays pass. The protected-category production promotion gate remains open.

The [pinned Ferrum audit](../../ferrum-prolog-release/docs/data/prolog-numeric-returns-20261116.json)
records frozen sources, artifact identities and separate search/checking times.
The [Ferrum ledger](../../ferrum-prolog-release/docs/state-of-the-art.md) records
the next family-sized cohort work and the limits of the current contract scan.

## Scalar-expression recurrent source states (2026-11-16)

CeTA integration `b42dba722aa68a27fc2a7ed33b2f211ae4757372` on
`codex/prolog-production-integration` adds a checked source nontermination
constructor for fixed scalar observations of growing arithmetic expressions.
The implementation is in `/work/dfm/festschrift/CeTA-prolog-release`.
`LP_Prolog_Scalar_Recurrence_NO` proves actual source nontermination using the
shared recurrent simulation theorem. Its checked interface retains earlier
clause failures, fresh-head resolution, cuts, pending continuations and saved
alternatives. Scalar template evaluation uses the existing exact integer and
binary64 profile. No source semantics or SEG is replaced.

`LP_Prolog_Scalar_Recurrence_XML` exports
`check_lpp_scalar_recurrence_xml`; the unified LP adapter accepts this constructor
through the regenerated `Prolog_Stable_Mixed_Generated` module. The executable
is `target/installed-prolog-scalar-recurrence-1514/ceta`, SHA-256
`19ffcdfe57894e070808f7aaabaa58e7cae8dc961249d8b3ab694eabb72aba2c`.
Verified export 1512 takes 401.544 seconds. Build 1514 rebuilds LP in 513.6
seconds and reuses the seven other category libraries. The export snapshot,
1,050 source hashes, copied verification log and installation receipts remain
under `target/prolog-scalar-recurrence-export-1512` and
`target/prolog-scalar-recurrence-install-1513`. Verified heap 1515 preserves the
new checked dependency closure. The supported stopped-mixed export script now
includes this constructor and call traces, with the established Array mapping
applied after imports.

Ferrum `6c2ad3701fb71fe88a771402546a505086948bc5` discovers ten additional
benchmark NOs with one witness-free action. The complete 221-root strict replay
retains every earlier verdict and reaches **86 YES + 62 NO**, with 148 authorized
receipts. LP-with-cut retains **84 YES + 9 NO** using this same executable.
The family passes 10 native and 10 strict checks, 12 advice/inapplicability
controls, 28 new complete-certificate checks, 106 legacy mutation checks and
25 packaged fixture replays. Isabelle checks positive and rejecting rule cases
and the eight initially targeted serialized benchmark certificates. The two
Ackermann roots are recovered by the same native implementation and checker.

The [Ferrum pinned audit](../../ferrum-prolog-release/docs/data/prolog-scalar-recurrence-20261116.json)
binds original sources, proof hashes, receipt hashes, timings, guidance and both
executables. The ten new binary64 witnesses also exceed bounded SWI-Prolog
execution limits. These results do not establish a matched-semantics comparison
with the saved AProVE YES records or satisfy the protected-category production
promotion gate.

## Scalar-domain recurrence with source entry (2026-11-16)

CeTA `456451b867552772f931c77f91ccd82e6b3b3b2a` on
`codex/prolog-production-integration`, in `/work/dfm/festschrift/CeTA-prolog-release`,
adds `LP_Prolog_Scalar_Domain_NO` and its proved XML constructor. Fixed scalar
observations and arbitrary evaluated integers form a recurrent interface.
Checked source entry traces establish its initialization. Exact clause
coverage, fresh `is/2` assignments and recursive argument dependencies preserve
it; the shared source recurrent-simulation theorem yields nontermination.
Unobserved arguments do not license arithmetic. Integer-domain closure admits
addition, subtraction and multiplication, not arbitrary float mixtures or
division. Existing SEG construction and return contracts are unchanged.

The unified LP adapter exports `check_lpp_domain_recurrence_xml` alongside all
previous constructors. Verified export 1528 takes 403.161 seconds. Build 1530
rebuilds LP in 529.6 seconds and reuses seven other category libraries.
`target/installed-prolog-scalar-domain-1530/ceta` has SHA-256
`17ab17045bcb3f8acb49aedbfcf898420c02f2de85d9c9ecbf282fce96e987e2`.
Source copies and 1,061 hashes, the frozen verification log, installation
receipt and verified heap 1534 remain on the persistent drive. Initial test
quoting, code-equation import and type errors are retained; corrected tests
1531/1533 pass, with no generated checking logic patched.

Ferrum `5b81709ce914dbddeff1c32ca4ee6363566ef64d` obtains 17 additional benchmark
NOs with one witness-free action. Full strict replay certifies **86 YES + 79 NO**,
retaining all earlier verdicts with 165 authorized receipts. LP-with-cut retains
**84 YES + 9 NO** using this identical checker. Validation includes seven
serialized benchmark certificates in Isabelle, domain rule controls, nine
native and nine strict family certificates, eight advice/inapplicability
controls, 38 new mutation checks, 106 legacy mutation checks and 27 packaged
fixture replays. SWI bounded runs time out on all 17 actual new witnesses.

The [pinned Ferrum audit](../../ferrum-prolog-release/docs/data/prolog-scalar-domains-20261116.json)
binds source, proof, receipt, guidance and executable identities. Ten saved
AProVE YESs in this cohort use an unmatched source/arithmetic profile; seven
saved results are MAYBE. No matched-profile superiority or protected-category
production promotion is claimed.

## Recurrent domain graphs across source predicates (2026-11-16)

CeTA `30fb9fefbcce6b1ddb66b504d71a82235c872ddf` on
`codex/prolog-production-integration`, in `/work/dfm/festschrift/CeTA-prolog-release`,
adds `LP_Prolog_Domain_Edge`, `LP_Prolog_Domain_Graph` and their source/XML
constructors. Checked source edges establish successor argument domains;
complete finite module coverage yields a recurrent set of actual source states.
Initialization remains an exact checked entry trace. Pending continuations and
saved alternatives are preserved. The source semantics and established SEG
remain unchanged, and no helper termination or successful-return contract is
inferred from recurrence.

The unified LP adapter exports `check_lpp_domain_graph_xml` alongside all older
constructors. Verified export 1540 takes 402.257 seconds; build 1542 rebuilds
LP in 547.0 seconds and reuses seven other category libraries.
`target/installed-prolog-domain-graph-1542/ceta` has SHA-256
`73fd97a3cc6c275eddd0ac12807fbaa93a2502169c63f353faff360e4e7ea141`.
The snapshot binds 1,067 Isabelle/export files; verified heap 1543 is saved.

The large serialized benchmark lemma in attempt 1539 was interrupted after
over ten minutes and is not counted as evidence. Its wrapper also exited;
verified heap 1534 was restored, and the five new theories and rule tests were
rechecked in resident 1544 before export. All benchmark certificates were then
checked by the verified unified executable and fresh strict replay. The
interrupted attempt and corrected proof-name/simplifier attempts are preserved.
No generated checking logic was patched.

Ferrum `8cfe8424b073391da3b8e0f3225e0e95ce1ad022` recovers eight benchmark NOs
with one witness-free action. Full strict replay certifies **86 YES + 87 NO**,
retaining all 165 previous results with 173 authorized receipts. LP-with-cut
retains **84 YES + 9 NO** using this identical checker. Validation includes ten
native and ten strict family certificates, ten advice/inapplicability controls,
54 new mutation checks, 172 legacy mutation checks and 29 packaged fixture
replays. Bounded SWI execution times out on all eight actual new witnesses.

The [pinned Ferrum audit](../../ferrum-prolog-release/docs/data/prolog-domain-graphs-20261116.json)
binds sources, artifacts, receipts, guidance and executable identities. A cut
in the recurrent prefix and a long finite inner-loop summary remain explicit
obligations. The unmatched arithmetic/source profile prevents a superiority
claim; protected-category production promotion remains separately gated.

## Integer quotient and modulo in recurrent observations (2026-11-16)

CeTA `32ce692648d54544a499868b034fb1d65be2a5b0` on
`codex/prolog-production-integration`, in `/work/dfm/festschrift/CeTA-prolog-release`,
adds `LP_Prolog_Scalar_Operations` and its rule controls. Existing scalar
expression/domain constructors now evaluate `//` and `mod` using the integer
operations already specified by the source profile. No source semantics or
established SEG definition changes. Zero and floating divisors remain rejected;
a changing integer numerator requires a fixed nonzero integer divisor.
Existing XML versions and processor guidance remain compatible.

Verified export 1548 passes in 406.751 seconds. Unified build 1550 rebuilds LP
in 528.5 seconds and reuses seven other category libraries.
`target/installed-prolog-scalar-quotient-1550/ceta` has SHA-256
`0803b0618bd4e373d8c9a5c707867d42402643888e8881c9fb1e861162787fef`.
The source snapshot binds 1,065 Isabelle/export files and verified heap 1551
is saved on the persistent drive. No generated checking logic was patched.

Ferrum `859701834f6100f390cf80d08522b045b32f596c` gains one benchmark NO,
`Weinert_15/division-nonterm.pl`. Full strict replay certifies **86 YES + 88 NO**,
retaining every previous verdict with 174 authorized receipts. LP-with-cut
retains **84 YES + 9 NO** using this identical executable. Validation includes
eight native and eight strict family proofs, 22 advice/inapplicability controls,
26 new and 226 legacy mutation checks, and 33 packaged fixture replays. The
four generalized fixtures exercise fixed and changing integer observations.
Bounded SWI execution agrees with the actual witness remaining active.

The [pinned Ferrum audit](../../ferrum-prolog-release/docs/data/prolog-scalar-quotient-20261116.json)
records source/proof/receipt identities, attempts and separate search/checking
times. Initial proof and test errors are preserved with corrected verification.
The complete per-root scan covers all 48 previous gaps, including source parser
rejections. Saved AProVE MAYBE is not upgraded from successful transformed NO
children. Matched-profile comparison and protected-category production promotion
remain open.

## Guarded-domain Prolog integration (2026-11-16)

Integration `c1eb7f090be8df4a38fcb3b8c7567d52bb4b2bf5` on `codex/prolog-production-integration`
adds version-1 `prologGuardedDomainGraphNonterminationProof` to unified Prolog
dispatch. `LP_Prolog_Guarded_Domain_Graph_XML` checks original source binding,
initialization, both exhaustive comparison branches and every referenced module.
Actual first-clause failure and source progress use the existing operational
semantics. All soundness dependencies pass the no-oracle/no-skipped-proof audit.
The established termination SEG and old constructors are unchanged.

Unified checker SHA-256 `fd4b9a0a94ae8c16524a4cdb8b24ec300680fa6548deddbe645b444d432b8d32` is frozen at
`target/installed-prolog-guarded-domain-1568/ceta`. Export 1566 and install 1567
bind the verified sources; build 1568 reuses seven category libraries. Verified
heap 1569 is saved. Ferrum `c2183099f6a3e5fc723104f49cdfee78ee687ed1` retains 86 YES +
91 NO over 221 roots and all 84 YES + 9 NO cut results, with
original-source audits, two checks and authorized reconstruction receipts.
300 mutation checks and 35 fixture replays pass.

Pinned evidence lives in the adjacent Ferrum checkout at
`docs/data/prolog-guarded-domain-20261116.json`. This is development integration;
matched-profile superiority and protected-category production promotion remain
pending. Initial failed proof/test/export attempts remain retained in the
resident log and the separate first export source capsule.

## Scoped cut recurrence integration (2026-11-16)

CeTA `1e55d2f9ee3a249ca2fdafd116b5d99cebf59ab7` on `codex/prolog-production-integration` extends the
existing version-1 guarded-domain checker with cut modules. The new prefix,
iteration, edge and module theorems execute the existing scoped pruning
operation and preserve the actual resulting saved stack. Source semantics and
the established termination SEG are unchanged. All soundness dependencies pass
the no-oracle/no-skipped-proof audit; multiple-cut and missing-coverage controls
pass independently.

Unified checker SHA-256 `7d9762f7d46859e096b3a6fee7d98c9c641af3b09d14e80ad7386e1cf147f4ed` is frozen at
`target/installed-prolog-domain-cuts-1590/ceta`. Export 1588, install 1589 and
LP-only build 1590 retain source identities and reuse seven category libraries.
Verified heap 1591 is retained. Ferrum `d71cc7f1d31daf024c8603ec49691d9868ffe7bc` certifies
86 YES + 93 NO over 221 roots, preserving all prior
results and all 84 YES + 9 NO LP-with-cut results. Original-source audits, two
checks, strict replay and complete authorized receipts cover every solved root.
336 mutation checks and 37 fixture replays pass.
Pinned evidence is in the adjacent Ferrum checkout at
`docs/data/prolog-domain-cuts-20261116.json`. Matched-profile superiority and
protected-category production promotion remain pending.

## Scope-invariant pending-goal source loops (2026-11-16)

CeTA `08da0a878d4bbc53702059f92f2dff7d9817d687` on `codex/prolog-production-integration` extends
`LP_Prolog_Checked_Builtin_Trace` and the binary64 source/XML/code interfaces
with complete goal cores. Scope invariance, nonempty checked execution,
barrier suffixes and source initialization instantiate the existing shared
barrier-pumping theorem. Old atomic certificates remain replayable; the
source semantics and established SEG are unchanged. The concrete executable
equation is proved from the locale definition. No soundness dependency uses
skipped proofs or oracles, and no generated logic was patched.

Unified checker SHA-256 `ebc745a4a5fd3c2e77b8d15ab70b56f28924c93bb39e7e2ad510df1e3695526c` is frozen at
`target/installed-prolog-goal-trace-1596/ceta`. Export 1594 and install 1595
bind the source snapshots; LP-only build 1596 reuses seven category libraries.
Verified heap 1597 is retained. Ferrum `27ba22834d2e485978499a70d4c04ceda49a24ca` certifies
86 YES + 94 NO over 221 roots, preserving all
179 prior verdicts and all 84 YES + 9 NO LP-with-cut results. Every retained
result has original-source audit, two unified checks, strict replay and an
authorized reconstruction receipt. There are
362 mutation checks and
38 fixture replays. Evidence is pinned in the
adjacent Ferrum checkout at `docs/data/prolog-goal-trace-20261116.json`.
Matched-profile superiority and protected-category promotion remain open.

## Ordered Prolog head failures (2026-11-17)

Proof commit `b9c6c45` and export integration `f24fc08` add checked failure
of earlier repeated-variable and linear nullary-constructor heads to the
existing recurrent source graph. Factored most-general resolution preserves
the caller continuation and fresh clause variables. False guards restore the
original saved alternatives; dummy constructor names cannot supply facts.
Old variable-head receipts remain replayable. Source semantics is unchanged.

The unified checker at `target/installed-prolog-head-failure-1608/ceta` has
SHA-256 `c8d0df480dfbe8caced3f146d605740ece426e89ac3497132c144f1d853b7c74`.
Isabelle export 1606 and LP-only build 1608 pass; seven category libraries
are reused. Verified resident heap 1609 is retained. Both new benchmark NOs,
`exercise_range.pl` and `extend.pl`, pass two checker runs and strict replay.
The fixed-221 campaign retains all prior verdicts at **86 YES + 96 NO**;
LP-with-cut retains **84 YES + 9 NO**. There are 414 mutation checks, 40
packaged fixture replays, and 701 passing shared native tests (26 ignored).
The [pinned Ferrum audit](../../ferrum-prolog-release/docs/data/prolog-head-failure-20261117.json)
binds original sources, reconstruction receipts, binaries and guidance.
Protected-category production promotion and matched superiority remain gated.

## Complete scalar disjunction failure (2026-11-17)

Proof commit `d34eb88` and export integration `cbe2375` on
`codex/prolog-production-integration` extend the existing recurrent source
checker with complete failed-choice trees. Both alternatives, identity-success
prefixes, the original clause head/body and restored saved stack are checked.
No soundness dependency uses skipped proofs or oracles. Source semantics and
the established SEG are unchanged; previous failure receipts remain replayable.

Unified checker SHA-256
`530ca389d5ecbf1f83c4d62fb2091a5bb19f168ef0d0b117e81968fd20100a11`
is frozen at `target/installed-prolog-failed-choice-1619/ceta`. Export 1617,
installation 1618 and LP-only build 1619 retain source identities and reuse
seven category libraries. Subsequent verified finite-input transport foundations
are retained in heap `target/prolog-finite-goals-1624-verified.heap`; they are not
yet a complete termination source bridge.

Ferrum `863f59eb` certifies the additional `factorial_or.pl` NO and retains all
previous results at **86 YES + 97 NO** over 221 roots. LP-with-cut retains
**84 YES + 9 NO**. Every solved root has original-source audit, two checks,
strict replay and authorized reconstruction. Validation includes 486 mutation
checks, 42 packaged fixture replays, three native/strict family proofs,
11 controls and 702 passing shared native tests (26 ignored). See the
[pinned Ferrum audit](../../ferrum-prolog-release/docs/data/prolog-failed-choice-20261117.json).
Priority 1 remains active. Matched superiority and protected-category production
promotion remain gated.

## Finite-input Prolog source root (2026-11-17, integration pending)

Resident checks 1648–1653 verify original-query initialization, a reachable
signature check against the complete source program, and the finite direct
XML soundness theorem. Unreachable library clauses are retained with original
indices; variable heads, missing reachable callees, unjustified initial free
facts and absent actions are rejected. This instantiates the shared finite
control induction and preserves the established graph and query modes.
No oracle or skipped proof occurs in the new soundness dependencies.

The adjacent Ferrum implementation consumes established residuals and routing.
It rejects open Split/module obligations and emits a closed control certificate.
Native fixture, audit and scheduler checks pass, including a divergent-root
control. Isabelle XML evaluation attempt 1654 was interrupted after 137 seconds
without a verdict. Unified export 1655 is in progress; no new accepted source
certificate, benchmark gain or production promotion is claimed here.

Finite-input source export 1655 and LP-only unified build 1657 now pass,
reusing seven category libraries. Verified heap 1658 is retained. Unified
checker SHA-256 `677c5501613c5706db34099e8cd719cead2d7392d4e2172ecc21bed64dc84311`
is frozen at `target/installed-prolog-finite-direct-1657/ceta`. It accepts the
original `sum.pl` certificate and its renamed fixture; fresh native and strict
runs pass two checks each. The fixed-221 replay reaches 87 YES + 97 NO,
retaining every previous result, and LP-with-cut retains 84 YES + 9 NO.
There are 184 authorized Prolog receipts, 524 mutation checks and 43 packaged
fixture replays. Source semantics and the established graph are unchanged.
Priority 1 remains active for checked module/Split assembly and its remaining
candidates. Protected-category promotion and matched superiority remain gated.

## Finite nonground comparison coverage (2026-11-17, export pending)

The comparison envelope now covers finite nonground compound operands as finite
errors, requiring both operands finite. This resolves the concrete unsupported
domain witness in resident attempt 1662 and SWI probe 2590 in Ferrum. Cyclic
operands remain excluded; groundness does not imply integer values. Existing
integer and binary64 operations are unchanged. The old comparison constructor
retains its ground-domain check.

The shared branch-link proof is factored from domain discharge. The finite-direct
source constructor supplies the checked finite-state invariant and retains all
success/failure/error links and saved contexts. Attempt 1665 verifies primitive
soundness and domain coverage. Attempt 1666 passes cyclic-term and compound
regressions but exposes an imported-constant collision in a new pattern variable;
1667 fixes it and verifies the complete original-query/XML soundness theorem.
No soundness dependency uses skipped proofs or oracles. The generated ML checker
accepts the generalized native fixture and rejects all five mutations (missing
success/failure/error links, wrong comparison direction, initial free fact).
Runtime generation/checking takes 57.990 seconds. The resident log and
`target/prolog-finite-comparison-runtime-1667/cases.json` retain every case.

No new unified export or benchmark gain is claimed. Installed checker 1657 and
its 87 YES + 97 NO preservation audit remain frozen. Priority 1 continues with
checked module/Split assembly and finite-state transport through more general
heads. Native integration and seven focused tests are in the adjacent Ferrum
checkout; its mechanism contract records attempts 2591–2595.

## Local finite head transport (2026-11-17, assembly pending)

Resident checks 1670, 1679–1680 prove finite transport through actual most-general
resolution, for fully ground selected calls with arbitrary heads and for partial
ground calls whose constructor positions are ground and standalone head variables
are separated from every other head argument. Fresh body-only variables remain
finite in the comparison unifier. Neither arbitrary rational substitution nor
an unconstrained input mode supplies finiteness or freeness evidence.

Checks 1685–1686 verify the executable head predicate, complete body/continuation
goal transport and six positive/negative regressions. Missing ground evidence,
sharing with a constructor position and repeated unconstrained head arguments
are rejected. Check 1695 verifies the local resolution-state checker against
all ordinary answer transitions, including saved alternatives and scalar
unification. The source program and actual clause indices remain explicit.

The shared finite action/control contracts now admit state-local stability
premises. Their previous globally stable forms remain proved compatibility
wrappers. Checks 1687 and 1690 verify both forms and recheck the complete existing
source/XML theorem. These changes have no skipped-proof or oracle dependencies.
They do not yet change the source root constructor or claim a benchmark gain.
Next assembly must discharge local static-signature and builtin-domain transport,
then retain all referenced module/Split and return-contract obligations.

Failed/interrupted attempts 1671–1678, 1681–1684, 1688–1689 and 1691–1694
remain in `target/prolog-domain-graph-resident-1544.log`: explicit type parameters,
quantifier instantiation, syntax/constant collisions and compatibility-wrapper
premises were corrected. Automated proof search in 1681 was interrupted after
43.617 seconds and replaced by a short structured proof. Only affected theories
were rechecked in the resident process; no unified checker was rebuilt.

Checks 1699 and 1701 complete local static-signature, builtin-outcome and
source-domain invariant transport, then compose those checks with the local
control-table contract. Each node uses only its checked ground variables and
context-derived ground facts; unknown external operations remain excluded.
Every boundary and actual-return obligation remains a premise. This removes
the global linear-variable-head requirement from the new local control theorem
without changing the existing root checker. Failed attempts 1698 and 1700
correct explicit theorem instantiation; the statements were not weakened.

Referenced triples assembly next needs the conjunction of finite-state evidence
and the existing triple-input instance invariant. Retain its scope/substitution
transport and the observed-evaluation normalization interface. Then instantiate
existing connection, return and Split contracts rather than introducing another
operational semantics or erasing incoming contexts. Neither these local proofs
nor checked child residuals count as additional certified benchmark roots.

## Finite local referenced assembly (2026-11-17, source integration pending)

Resident checks 1704, 1707–1710 generalize the existing observed-evaluation,
local action and control contracts with an additional invariant. The previous
forms remain compatibility wrappers. Instantiation retains both finite current
and saved goals and the existing triple-input instance invariant. Connections
transport finiteness through their checked substitution/scope equality; they
make no claim about finiteness of unobserved answer-interface values.

Checks 1712–1713 verify region assembly and referenced graph composition.
Check 1717 verifies child and Split assembly, retaining complete interfaces,
actual-return coverage and both descent obligations. Its continuation requires
finite-state evidence for actual successful returns, separately from helper
termination. Check 1719 supplies an executable dependency predicate for such
continuations; finite or ground facts must cover every used term variable and
the static signature must cover each called predicate. Existing source return
contracts still need to discharge these facts in the complete root constructor.

Check 1720 passes five return-dependency regressions and the complete existing
source/XML soundness theorem. Missing dependencies, missing signatures and
unrestricted dynamic calls are rejected; unused answer values stay unrestricted.
Every new soundness theorem passes the no-oracle/no-skipped-proof audit. All
checking used the resident process; no unified rebuild or new benchmark verdict
is claimed. The installed 1657 checker and 87 YES + 97 NO audit remain unchanged.

Failed attempts are preserved in `target/prolog-domain-graph-resident-1544.log`:
1705–1706 fix syntax/explicit invariant instantiation, 1711 fixes a definition
name, 1714–1716 diagnose an accidental extra local premise in the Split proof,
and 1718 replaces unsuccessful automation with explicit per-goal instantiation.
The verified Split theorem does not contain the accidental premise. Next wire
checked return facts and local region checks into source graph/root assembly,
then native emission, residual discharge and strict benchmark replay.

Verified heap `target/prolog-local-assembly-1721-verified.heap` saves assembly
through 1720. Follow-up 1723 also derives continuation finiteness directly from
checked outgoing ground/context facts and the executable dependency predicate,
allowing existing actual-return contracts to discharge that obligation. Attempt
1722 used the reserved keyword `context` as a fact label; renaming the label
fixes parsing without changing the theorem. Five continuation regressions pass
again. Concrete preserved/integer/ground return-family adapters and the root
constructor remain the next integration work.

Resident checks 1725–1730 complete preserved, integer, ground and shape
actual-return adapters, local component/descent assembly, the original-query
root theorem, and mixed backend/XML composition. The new constructor
`prologEstablishedFiniteLocalSEGMixedProof` retains the existing referenced
component datatype, transfer contracts and common backend routing. It has not
yet been exported to the unified executable. No benchmark gain is claimed.

Runtime attempt 1731 exposed a non-executable existential in the static source
predicate. An equivalent proved code equation fixes this; the partial equation
in 1732 caused a match exception on cuts, and the exhaustive equation in 1733
passes runtime generation. The same three native artifacts from Ferrum 2601
then show complete source-assembly acceptance for `division.pl`; the list-length
and gcd candidates reject finite-head side conditions. The latter are genuine
remaining source obligations, not residual solver failures. Full generation
and evaluation in 1733 took 153.916 seconds. All failed attempts remain in the
resident log.

Checks 1735–1736 prove and integrate finite-ground-template resolution:
a finite selected call may unify with a ground clause head without every call
argument already being ground. A finite comparison substitution and actual
most-generality preserve the body and continuation; arbitrary rational
substitutions are not assumed finite. Attempt 1734 exposed a missing theory
import and is retained. The general extension is motivated by a rejected base
clause, with no benchmark dispatch in the checker. The source assembly cohort
and head regressions are being rerun in 1737 before unified export.

Runtime 1737 accepts both division and list-length source assemblies; gcd
retains three finite-head failures. Ten head regressions pass. Follow-up
1741–1743 generalizes the proof to head variables covered by ground actual
arguments: checked coverage makes the successful head instance ground, and
finite comparison substitutions preserve body and continuation through the
actual MGU. Twelve head regressions pass, including repeated-variable coverage,
missing-anchor rejection and cyclic-binding rejection. This intentionally turns
one former conservative rejection into a checked acceptance. Attempts 1738–1742
retain syntax and type-instantiation errors; 1740's broad Metis search was
interrupted after 26.481 seconds and fixed by separating template-variable
and runtime-variable types. Runtime cohort 1744 and incremental export 1745
are pending; the old unified checker remains installed.

Runtime 1744 accepts all source-assembly checks for division, list length and
gcd using the exact original native 2601 artifacts. These are source checks
only, with residual backends deliberately absent. Export 1745 is underway;
no installed checker or certified benchmark count has changed.


## Observed row composition foundation — 2026-11-17

Resident check 1762 verifies complete Cartesian row-pair coverage and termination
transfer in `LP_Prolog_Stable_Row_Composition.thy`. Every two consecutive observed
calls is covered by a composed row. Termination of the composed relation implies
termination of the original relation by sampling alternate elements of any infinite
chain. Both successful prefixes, guards, observations and rational interface
equations are retained. Variable-prefix freshness is checked for every input row.
All new soundness dependencies pass the no-oracle/no-skipped-proof audit.

Attempts 1755–1761 are retained in the resident log: automatic existential proofs,
a missing singleton lemma, and union instantiation were replaced with explicit
membership witnesses. Attempt 1758's broad search was interrupted after 29.205
seconds. Check 1762 completes in 3.268 seconds in the resident heap.
This foundation is not yet exported or connected to common component routing.
The latest exported integration remains 14130e9 (89 YES + 97 NO in Ferrum's
complete strict replay); division and numbervars remain open priority-1 roots.


Resident checks 1763–1771 integrate finite sequences of checked compositions
with common numeric/structural backends and finite-local source/XML assembly.
The `composedBackend` wrapper records freshness stages and its explicit child
rows. A checked row-wise equality preserves endpoint atoms and the sets of all
helper premises, guards and observations; it permits serialization reordering
without dropping assumptions. Legacy backends decode with an empty stage list.
The complete source soundness and inherited-oracle audits pass at 1771.
Attempts 1765–1770 retain proof automation, list lemma, reserved `rows` binder
and type-instantiation corrections. No export or unified rebuild has run yet.
Native residual probes will determine whether the composed abstraction is
precise enough before generating another checker.


Checks 1772–1777 strengthen composition with proved static predicate/arity
compatibility and existing checked equation normalization after each stage.
Runtime substitutions preserve the predicate and arity of the intermediate atom,
so only incompatible interfaces are excluded. Rationally cyclic equations remain.
Interface equations orient fresh right-head arguments toward the previous call,
allowing the existing bounded normalization to expose later arithmetic observations.
Each stage records freshness and normalization fuel; the full source/XML theorem
and inherited-oracle audit pass at 1777. Attempts 1772–1774 retain an unconstrained
runtime-type witness and an image-membership proof correction. No checker export
or benchmark gain is claimed from these proof checks alone.


Resident check 1778 adds the existing checked endpoint rewrite after observation
normalization in each composition stage. Both transformations use the recorded
fuel and preserve the observed-call relation by inclusion; the complete source
and XML soundness theorem passes. This exposes interface-equal values at the
actual residual head/call rather than only as side observations. Existing
rational-equation semantics and all helper/return premises are retained. This
proof change is not yet exported to the unified checker.


Observed quotient evidence: checks 1780–1781 prove the truncating quotient bound
from successful evaluated-integer observations and integrate it into the existing
quotient path receipt. Both numerator signs retain the existing piecewise formula;
groundness alone is insufficient. Attempt 1779 used reserved proof label `term`;
1780 needed explicit instantiation of the existing receipt theorem, fixed in 1781.
Composition equivalence additionally ignores only `LPPSOpaque` markers, whose
success-guard interpretation is True; actual observations and nontrivial guards
remain checked. Its composed-backend theorem has passed during 1782; source
rechecking and actual-certificate runtime check 1783 are still in progress.

Ferrum native candidates 2645–2646 close division residuals via the existing
magnitude backend and compose complete source certificates. The installed 1747
checker predates the wrapper and rejects it. No new certified verdict or export
is claimed before source/runtime validation and unified replay.


Runtime 1789 verifies all five source/composition checks on each complete native
division candidate 2645 and 2646. This corrects the premature statement above:
1782–1784 required explicit guard cases and set-level proof rewriting; 1785
then passed source proofs but failed executable set-equality generation. A
proved bidirectional membership code equation fixes generation without changing
the logical predicate. Runtime 1789 passes in 160.850 seconds. Numeric child
checking and unified replay remain pending. Prepared export 1786 never ran;
its build waiter was stopped without starting compilation.


## Constructor argument observations — 2026-11-17

Resident check 1798 verifies `LP_Prolog_Constructor_Arguments.thy`, including
exact constructor labels and children, arity from observed list length,
substitution transport, and equivalence of whole-term/whole-argument-list
finiteness. A cyclic-child control proves that a one-element argument spine
does not make its cyclic element finite. All dependency checks reject oracles
and skipped proofs. This theory is not included in export 1790 or build 1792.
Checked source `=..` coverage, name translation, context transport and Split
interfaces are still required before it can certify numbervars.

Attempts 1793 and 1795–1797 retain a name collision with the existing `args`
constant and unsuccessful automatic cyclic-membership proofs. Explicit
constructor injectivity and occurrence-specific substitution fix the latter;
1798 passes in 0.837 seconds. Native replay correction `dff72065` independently
passes 710 shared LP tests and advances numbervars to its semantic-projection
obligation. No new benchmark result is claimed by these observation lemmas.

Export 1790 passed in 444.823 seconds; LP-only unified build 1792 reuses seven
unchanged category libraries. The original source/composition runtime checks
passed at 1789. Complete backend checking and strict replay remain pending.


## Checked row composition unified integration — 2026-11-17

Export 1790 and LP-only build 1792 integrate complete compatible row composition,
checked normalization/endpoint rewriting and observed truncating-quotient
evidence. Proof baseline is `79b62b8`; the later constructor-argument theory
is not exported. The unified checker SHA-256 is
`9544310fafd19a83aedc889f42bc9beb1258f865e22aad0bab7382f828b3b0b2`.
Build 1792 takes 525.7 seconds for LP and reuses seven category libraries.
No generated checking logic was edited manually.

Ferrum native `dff72065`, frozen build 2656, strictly replays all 221 Prolog
roots to **90 YES + 97 NO + 34 UNKNOWN**, preserving all 186 previous verdicts.
The new YES is `Weinert_15/division.pl`. All 187 solved roots have original-source
audits, authorized complete reconstruction receipts and two passes by this
checker. The same executable preserves **84 YES + 9 NO** LP-with-cut results.
Family 2653 includes the original division source and a renamed divisor-three
fixture, strict replay, missing/conflicting guidance and seven divergent controls.
Checks 2655, 2659, 2662 and 2663 pass all 652 mutations; 2660 passes 46 packaged
fixture replays. A fresh Split fixture also passes native/strict replay.

The integration is recorded in `scripts/unified-exports.json`; full evidence
will be pinned in Ferrum's `docs/data/prolog-composed-20261117.json`. Priority 1
still includes numbervars. Protected-category production promotion and matched
superiority remain separate gates, not claims of this category integration.


Check 1800 extends constructor arguments with the explicit named functor
observation used by native projection candidates. It proves substitution
transport, ground names, finite argument spines, and equivalence of whole
argument-list/term finiteness. Constructor-name encoding is an explicit parameter
that still requires profile-specific instantiation; these lemmas do not assert
source `=..` coverage. The no-oracle/no-skipped-proof audit passes. Attempt 1799
collided with the existing `name_of` constant and is preserved. No export or
checker rebuild includes this unfinished source integration.


## Univ decomposition and functor context transport — 2026-11-17

Resident check 1814 verifies `LP_Prolog_Univ_Decomposition.thy`: nonvariable
constructor decomposition, success observations from shared rational MGU,
normal-failure exclusion and retention of terminal error outcomes. An executable
domain check accepts constructor inputs or a checked free output list/name;
unknown output lists and known-name construction from a variable input remain
unsupported. Five positive/rejection lemmas pass. The outcome relation is a
termination overapproximation, not a claim that every retained error occurs.
Constructor-name encoding remains an explicit parameter needing source-profile
correspondence. Saved alternatives use the existing answer transition unchanged.

Check 1818 verifies `LP_Prolog_Functor_Context.thy`: explicit value/name/argument
facts, acquisition on successful decomposition, runtime substitution, checked
instance transport and the existing resolution environment's refresh operation.
Identity transport passes; removing a fact or changing its name/argument list
rejects. Both theories pass no-oracle/no-skipped-proof dependency audits.
Attempt 1815 collided with Isabelle's factorial constant `fact`; 1816 had a
lexical spacing error in a bound. Corrected transport passes 1817 and acquisition
plus controls pass 1818 in 7.532 seconds. No full rebuild was used.

SWI-Prolog 9.0.4 counterexample 2670 in the Ferrum tree establishes why input
finiteness alone cannot be transported through univ: `T=f(X), T=..[f|X]`
starts finite and ends cyclic, while the argument list still has length one.
Fresh/nonalias output evidence must therefore be checked before asserting
post-state finiteness. These theories are not exported and do not change the
90 YES + 97 NO certified baseline. Complete source-profile coverage, per-frame
assembly, finite-domain preservation and Split contracts remain integration
obligations for numbervars.


Finite univ follow-up: `LP_Prolog_Finite_Univ.thy` passes resident check 1825
with no oracles or skipped proofs. A finite constructor input and two distinct
output variables absent from its runtime support admit a finite comparison
unifier. Shared MGU factorization then preserves all finite active continuation
terms. The runtime-support assumption rejects the SWI aliasing counterexample;
input finiteness or output freeness alone is insufficient.

`LP_Prolog_Finite_Fresh_Body.thy` connects this condition to source resolution.
A body-only variable cannot occur inside the finite instantiated head under the
shared most-general-resolution semantics. The executable clause-side check
requires the input variable in the head and two distinct body-only outputs;
its theorem establishes free, distinct runtime outputs absent from the input.
Check 1834 passes in 1.295 seconds, including a generic positive clause and
missing-output, input-alias and output-alias rejection lemmas. This evidence is
at clause entry; it must not be assumed preserved by arbitrary intervening
unification. Source-node transport and parent assembly still require integration.

Attempts 1819–1824 retain induction, binder/definition and theorem-instantiation
failures; 1825 completes finite-univ verification. Attempts 1825–1827 then expose
fixed-variable and environment-instantiation proof gaps, corrected at 1828.
Clause-side checks 1829–1832 retain existential proof and lexical corrections;
1830's broad proof search was interrupted after 13.526 seconds and replaced
with explicit witnesses. Checks 1833–1834 pass the full fresh-body theory and
dependency audit. No export or unified checker rebuild was performed, and no
new benchmark verdict is claimed.


Univ source normalization: check 1839 verifies
`LP_Prolog_Univ_Normalization.thy`. The existing answer machine's constructor
view reduces to its shared equality step, preserving the exact continuation and
saved answers on success/failure and discarding the stack on uncaught errors.
The theorem lifts the equality child's full answer contract to the source call;
variable-input view outcomes are checked terminal errors. Builtin selection,
source-domain membership and source-outcome coverage remain explicit premises.
No new machine or SEG is introduced. Named constructor interpretation still
needs its profile-specific correspondence before source acceptance.

Check 1836 completes transition coverage, 1837 adds the return contract and
1839 covers unknown inputs. Attempt 1835 needed explicit specialization of
outcome coverage; 1838 had ambiguous theorem instantiation, fixed with an
explicit name parameter. Final check 1839 passes in 2.975 seconds with a clean
no-oracle/no-skipped-proof dependency audit. These proofs are not exported and
no new root verdict is claimed. Native discovery of the established view must
retain both equalities, all frames/answers and the terminal error branch.


Shared return links with functor evidence: resident check 1841 verifies
`LP_Prolog_Functor_Link.thy`. The extended checker uses the existing return-table
link, old context transport and explicit functor transport under exactly the
same binding substitution. Its target context and functor evidence are selected
by the checked state's target index. The soundness theorem retains state equality,
knowledge, prior source facts, functor facts and the original residual edge.
Missing contexts, out-of-bounds targets, missing facts and changed argument facts
reject. An empty-extension equivalence retains the old link/context obligations.
Check 1840 passes the main theorem; 1841 passes controls and the dependency audit
in 0.603 seconds. No oracles or skipped proofs occur.

Ferrum's complete-state projection candidates now retain a separate observation
record for each saved frame and guard namespace. Focused 2674 and all 13 native
projection tests 2676 pass (one manifest diagnostic intentionally ignored).
Original-source diagnostic 2675 projects all 69 established numbervars states
without an unsupported projection, with two frame-local functor relations; both
univ receipts remain present. This is native candidate coverage, not checked
local-table initialization, source acceptance or a new benchmark verdict.
The new link is not yet exported; source action initialization, freshness
transport, Split/return contracts and parent residual assembly remain required.


Univ initialization: resident check 1850 verifies
`LP_Prolog_Univ_Initialization.thy`. Fresh projected value/name/argument variables
are interpreted using the actual constructor input, establishing the precise
functor relation and the first equality. The full original saved state, old
source context and earlier functor facts are preserved. Capture checks reject
aliased observation names, saved-answer capture and capture of prior facts.
The shared equality identity step connects the established two-equality view
to the source answer contract; it does not delete an unchecked failure branch.

The initialization also preserves existing ground/free knowledge and guards.
The name becomes ground; arguments become ground only with an explicit ground
input premise. No integer fact follows. The existing source-domain and outcome
coverage premises, name interpretation, local-table wiring and Split assembly
remain outstanding integration obligations. The source theories are not exported.

Check 1846 passes initialization, two-equality composition and capture controls;
1849 adds knowledge preservation; 1850 verifies conditional argument groundness
and the dependency audit in 4.723 seconds. Attempts 1842–1845 retain a reserved
proof-label correction and explicit theorem-instantiation fixes. Attempts
1847–1848 correct definition parameters and the shared machine's runtime-variable
type. No oracle or skipped proof is present, and no full rebuild was performed.


Checked local univ action: `LP_Prolog_Univ_Context.thy` combines source shape and
domain checking, fresh observation initialization, exact two-equality successor
representation, knowledge preservation and a checked child link into an answer
contract for the original source operation. Its lower-contract premise requires
the actual residual edge, target state and all target ground/free/context/functor
facts. Terminal variable-input errors and normal unification failure retain the
previously proved coverage. The rule uses the shared answer machine throughout.

`LP_Prolog_Functor_Free_Link.thy` layers the existing normalized freeness check
onto the functor link. The base link now exposes its exact target environment,
so the freeness and observation proofs cannot choose different witnesses. Check
1851 passes this extension. Check 1853 verifies the initialized successor state;
1858 verifies the full local contract; 1859 adds rejection controls for missing
domain evidence, aliased observations, missing child states and saved-answer
capture. The final check takes 10.876 seconds and passes the clean dependency
audit. Attempts 1852 and 1854–1857 preserve controlled rewriting, lexical spacing,
groundness instantiation and root-state unfolding corrections.

These local rules are not yet a table constructor or exported source certificate.
The current context theorem uses the established integer-context interpretation;
wiring into the stable source route must also use its parameterized evaluation
context/link infrastructure wherever numeric observations require binary64
coverage. Integer evaluation assumptions cannot be substituted for that coverage.
Source profile/name correspondence, finite invariants, helper return/Split
assembly and complete residual discharge remain open. No benchmark gain or
unified checker rebuild is claimed.


Parameterized evaluation and functor evidence: the shared evaluation-link
witness now admits an auxiliary predicate proved at its exact instance valuation.
The original theorem remains a compatibility corollary with the same statement.
`LP_Prolog_Evaluation_Functor_Link.thy` uses this hook to check functor transport
alongside the existing evaluation context, free knowledge, scope swaps and
residual edge. Missing functor tables/facts and changed arguments are rejected;
an empty extension reduces to the existing link plus explicit table bounds.
Check 1860 verifies the generalized witness; 1862 verifies the extension and its
controls in 2.176 seconds. Attempt 1861 needed an explicit predicate instantiation.

`LP_Prolog_Univ_Evaluation_Initialization.thy` reuses the existing state/functor
initialization proof and separately preserves the full parameterized evaluation
context by checked freshness. The empty context in the auxiliary reuse only
extracts context-independent conclusions; the actual source context is retained
and proved unchanged. No integer interpretation is imposed on evaluation.
Check 1866 passes all four conclusions and the no-oracle/no-skip audit in 1.683
seconds. Attempts 1863–1865 record empty-context unfolding and theorem-bundle
audit syntax corrections. Evidence remains in
`target/prolog-domain-graph-resident-1544.log`. Only affected theories were loaded;
no export, executable rebuild or benchmark gain is claimed. The local action's
parameterized-context assembly, source table/profile connection and residual
proof remain open.


The parameterized local univ contract is now checked in
`LP_Prolog_Univ_Evaluation_Context.thy`. It combines the existing projected
successor, initialization and evaluation/functor child link while retaining the
source domain, outcome coverage, free knowledge, guards, saved answers and lower
answer-contract obligations. Check 1867 passes the full contract, initialized
state correspondence, missing-domain/aliased-observation/missing-child/saved-
capture rejection controls and dependency audit in 12.778 seconds. The resident
session completed before a subsequent interrupt; the success marker is present
in `target/prolog-domain-graph-resident-1544.log`. No export or full rebuild ran.

Integration remains incomplete: `lpp_stable_source_builtin` currently delegates
univ to the finite/legacy interpretation, which has no univ-domain coverage.
The new local contract's coverage premise therefore still needs an explicit
source interpretation extension and original-source audit. The constructor-name
map must respect arity-dependent reserved builtin encoding in native
`static_source::encode_symbol`; removing an arity prefix is insufficient.
The existing graph/table representation must also carry the new observations
through all intervening actions and Split contracts before residual certification.


`LP_Prolog_Univ_Source.thy` now extends the builtin/domain interpretation of the
same shared source machine with univ view outcomes. It proves exact agreement
on every old finite-source domain, preserves all other operations, checks the
fixed builtin signature and rejects wrong arities. Construction from a known
functor with variable input remains outside the admitted domain. The local
contract is instantiated with these actual domain/outcome definitions, discharging
its former abstract coverage premises. Check 1872 passes the interpretation,
compatibility, local contract and inherited-dependency audit in 5.994 seconds.
Check 1870 verified the interpretation alone; 1868–1869 record a broad signature
simplification replaced by explicit cases and concrete character evaluation;
1871 records an explicit higher-order premise discharge. No full rebuild ran.

The name map stays universally parameterized, not certificate-supplied. A future
root theorem valid for every map can be instantiated with the original-source
encoding without choosing a convenient witness or discarding names. This does
not itself complete that root theorem or original-source correspondence audit.
The native arity-dependent encoding remains authoritative; any concrete name
projection must account for reserved names at arity zero as well as at the input
arity. Existing source strategies/exports are unchanged. Complete graph action
transport, module/Split interfaces, finite structural measures and residual
proofs remain required before a benchmark certificate can be claimed.


Functor transport through shared unification and resolution is now formalized.
`LP_Prolog_Functor_Fork.thy` proves that the existing resolution environment
simultaneously preserves original observations for saved alternatives and
refreshed observations after successful substitution, with explicit variable
bounds. `LP_Prolog_Functor_Representation.thy` binds these facts to the same
state index, valuation, arithmetic context, free knowledge and residual edge.
The link retains the existing alternatives for active and saved freeness.

`LP_Prolog_Functor_Equality.thy` and `LP_Prolog_Functor_Resolution.thy` extend the
existing local action checks with that representation. They use the shared MGU,
return payload and scope machinery; failure resumes the old context, not the
successful fork. The Boolean checks require both branches unless the existing
coverage rule discharges one. Missing functor tables and unbounded source facts
are rejected. Check 1876 passes equality, 1878 resolution, and 1879 both actions
with controls and dependency audits (resolution 2.499 seconds). Attempts
1873–1875 preserve lexical spacing, an overbroad argument replacement and
explicit higher-order proof-premise corrections; 1877 records a missing functor
argument in an intermediate proof statement. Evidence is retained in the
resident 1544 log. No oracle admission, generated checker edit or full rebuild
was introduced.

These remain unexported proof components. Remaining graph work includes other
local actions, normalized functor transport where required, initialization and
complete table coverage, module/Split interfaces and finite structural residual
measures. No new root certificate or benchmark gain is claimed.


Functor-aware administrative and allocation actions now reuse the shared cut
machine's exact next state, scope swaps and return-event checks.
`LP_Prolog_Functor_Admin.thy`, `LP_Prolog_Functor_Allocate.thy` and
`LP_Prolog_Functor_Cut_Actions.thy` retain functor relations in the same child
valuation as arithmetic contexts and ground/free knowledge. The dispatcher uses
the existing action datatype, including terminal, inconsistent, administrative,
case, meta-call, equality and resolution actions. Checks 1880–1881 pass these
proofs; 1883 includes missing-table rejection and dependency audits.

`LP_Prolog_Functor_Term_Test.thy` checks term tests on both outcomes, proves exact
operation correspondence for the extended univ source interpretation and proves
the source domain admitted. Failure keeps the incoming facts on the resumed
saved alternative. Check 1884 passes the proofs, missing-table control and audit
in 3.646 seconds. Attempt 1882 needed controlled rewriting of the existing
source-comparison correspondence rather than expansion of all comparisons.
Only affected resident theories and invalidated dependencies were loaded; no
full rebuild, export or checker executable change occurred. Evidence remains
in the resident 1544 log.

The candidate still requires arithmetic actions with functor preservation,
normalized fact projection where needed, complete table and module/Split
composition, finite structural measures and residual discharge. These checks
are not benchmark certificates and do not change the certified baseline.


Arithmetic observation with functor facts now preserves the full stable context.
`LP_Prolog_Stable_Link.thy` exposes an auxiliary-observation witness at the exact
checked child valuation; the old theorem remains a compatibility corollary with
its unchanged statement. `LP_Prolog_Stable_Functor_Link.thy` uses this witness so
stronger stable comparison observations are retained along with functor facts.
Attempt 1885 exposed that the generic evaluation-context witness alone does not
establish those stronger observations; the implementation uses the existing
stable transport proof instead of weakening the target context.

`LP_Prolog_Functor_Observed_Is.thy` checks fresh scalar-result initialization,
including freshness against every prior functor fact, and transports the
synthetic equality child with full stable context and functor evidence. Missing
fact tables and result capture are rejected. Check 1886 passes the observation
proof and controls. `LP_Prolog_Univ_Arithmetic_Normalization.thy` connects the
extended interpretation's is/2 operation to the existing stable arithmetic and
shared equality transition. It retains unification failure and terminal errors.
The resulting full local answer contract passes in check 1887 (3.567 seconds
for the observed-is theory), with dependency audits. The source-domain premise
is still explicit; groundness is not used as an integer assumption.

No exported source constructor or benchmark gain is claimed. Complete table and
Split composition, stable-context preservation across the other action wrappers,
finite structural invariants and residual discharge remain open. These generic
and stable context variants must not be interchanged without their correspondence
proof. Only affected theories and invalidated resident dependencies were checked;
no full build or generated checker edit occurred. Evidence remains in the
resident 1544 log.


Full stable-context closure of the local action layer: the same Boolean checks
now have proofs for the stronger stable context together with functor relations.
`LP_Prolog_Stable_Functor_Representation.thy` binds both interpretations to the
same node index and checked child valuation. `LP_Prolog_Stable_Functor_Actions.thy`
proves equality, resolution, administrative steps, clause/meta allocation,
the shared cut-action dispatcher and source term tests with that representation.
No checker datatype or graph construction is replaced. The existing stable
fork and equation-observation proofs retain comparison information on success
and the prior context on failure.

`LP_Prolog_Univ_Stable_Initialization.thy` and
`LP_Prolog_Univ_Stable_Context.thy` extend initialization and the local univ
answer contract to full stable contexts. Check 1890 passes all four theories and
dependency audits (univ context 4.370 seconds). Attempt 1888 corrected a renamed
definition declaration; 1889 removed an inadvertently duplicated meta-check
definition from the proof wrapper, leaving the existing checker authoritative.
Evidence remains in the resident 1544 log; no export or full build ran.

The next obligation is parent assembly rather than more local operation variants:
construct a complete table contract with the extended source interpretation,
retain every module/Split dependency, establish required finite observations on
actual returns, and discharge the structural residual. Complete source/name
correspondence, native serialization, strict replay and benchmark certification
remain unproved. The high-water mark is unchanged.


The functor local proof table is now explicit in
`LP_Prolog_Functor_Control_Check.thy`. Its action datatype references the existing
cut actions and checked term-test, observed-is and univ links. The table requires
matching lengths for states, contexts, free facts, functor facts and actions,
checks each state's established node identity, and exposes every Some action's
check. None remains a module-boundary obligation; it is not a solved node or a
termination result. Existing tables and strategy atoms remain unchanged.

Check 1893 passes complete-entry extraction, missing-action/missing-fact-table
and state-mismatch rejection, wrong univ arity rejection and the arithmetic
source-domain theorem in 6.947 seconds. The latter derives ground expression
evaluation from checked incoming observations without assuming integer values.
Attempt 1891's overlapping function patterns were interrupted after 41.390
seconds and replaced by explicit case dispatch; 1892 verified that table in
6.606 seconds. No operation coverage was removed by this implementation change.
Evidence remains in the resident 1544 log.

The table's global answer-contract theorem and module boundary composition are
still required. The Boolean table check alone is not exported as a source
certificate. Original-source audits, finite invariants, residual solving and
strict replay remain outstanding, so no benchmark gain is claimed.


The parent-contract layer now begins in `LP_Prolog_Functor_Control_Contract.thy`.
It connects the dispatcher control and term-test cases to full answer contracts
for the extended source interpretation. Each successor requires its exact scoped
representation, residual descent and preserved invariant; the shared contract
start theorem transports its return obligation back to the caller. Administrative
return events use the checked emit relation. These are contract proofs, not
termination claims about unchecked children.

This integration exposed a missing side condition in the unexported dispatcher:
ordinary cut actions must satisfy `lpp_no_builtin_frame`, except for the checked
inconsistent-state case. The dispatcher now uses the same guard as the established
source primitive rule, with a rejection lemma. Otherwise a builtin could be
processed as an ordinary predicate. No installed checker or retained certificate
used the incomplete candidate. Check 1895 verifies the source bridge and control
contract; 1896 adds the term-test contract and passes the audit in 1.843 seconds.
Attempt 1894 corrected an extra parenthesis in the theorem statement. Evidence
remains in the resident 1544 log; no full build ran.

Arithmetic/univ dispatcher contracts, the global table theorem and explicit
module-boundary/Split composition remain open, followed by finite invariants,
residual discharge and strict replay. No new root verdict is claimed.


All four current dispatcher cases now have local source answer contracts.
`LP_Prolog_Functor_Control_Contract.thy` adds observed arithmetic and univ
contracts, explicit target-table bounds and introduction of the scoped module
representation with full stable and functor contexts. Lower contracts are lifted
to the caller only along the checked residual edge. Arithmetic obtains its
source domain from the Boolean check; no integer-input assumption is added.

The univ local theorem now has an invariant-aware version. Its normalization
premise must establish the invariant on the actual two-equality successor, which
is then transported to the exact checked target. The prior theorem remains an
unchanged compatibility corollary using True. This makes finite-observation
obligations explicit rather than treating termination children as return or
finiteness proofs. Check 1900 verifies both dispatcher contracts, compatibility
and dependency audits in 7.531 seconds. Attempts 1897–1899 record explicit bound
extraction, controlled higher-order premise application and the shared runtime
valuation type. Evidence remains in the resident 1544 log.

The global table theorem, module/Split boundary contracts, concrete finite
invariant discharge and structural residual remain open. No native certificate,
checker export, full rebuild or new benchmark verdict is claimed.


`LP_Prolog_Functor_Table_Contract.thy` now proves whole-table answer-contract
composition using the shared `lp_answer_contract_modular` theorem. Its root
requires residual termination, all incoming ground/free/stable/functor facts,
and the invariant. Scope renaming preserves that invariant explicitly. Every
Some action requires its node contract; every None entry separately requires a
module-boundary contract. The theorem never interprets a missing action as a
successful proof. Four introduction lemmas connect the existing checked cut,
term-test, observed-arithmetic and univ contracts to these node obligations.
Arithmetic and univ normalization invariants remain explicit proof premises.

Resident check 1906 passes the table theorem, all four introductions and the
inherited-oracle/no-skip dependency audit in 1.775 seconds. Evidence remains in
`target/prolog-domain-graph-resident-1544.log`. Attempt 1901 was interrupted during
higher-order representation inference; explicit instantiation resolves it.
Attempts 1902–1905 corrected reserved proof labels, the dependency-audit argument
type and explicit invariant instantiation. No build limits were raised and no
full build or checker export ran.

This is a conditional assembly theorem, not an executable source certificate:
Split boundary contracts and their finite referenced dependencies, concrete
finite-observation invariants, original-source/name correspondence, native
serialization, residual discharge and strict replay remain required. The fixed
population remains 90 YES, 97 NO and 34 UNKNOWN; numbervars.pl remains UNKNOWN.


The functor table's node contract now receives residual termination at its own
subject. Check 1907 verifies propagation from the root and along strict residual
edges (1.805 seconds). This is needed by Split/module contracts; it does not
assume termination independently or remove any root residual obligation.

`LP_Prolog_Functor_Split_Contract.thy` applies the shared actual-answer composition
theorem to the extended source interpretation, with checked original Split
routing and checked return projection. A separate actual-return predicate carries
helper properties into the continuation. No obligation is imposed only on an
unchecked abstract return, and helper termination does not establish that
predicate. The same theory proves preservation of initialized functor relations
through actual returns, jointly with full stable contexts and finite observed
spine length. Every incoming frame must establish the observations; free facts
and finite trees are not claimed to be substitution-invariant.

Check 1911 passes these three theorems and their dependency audit in 3.482 seconds.
Check 1910 verified composition alone. Attempt 1908 was interrupted in an
unnecessary historical module-semantics import; the final theory imports only
the shared routing/composition dependencies. Attempt 1909 fixed the explicit
string type of projection-interface variables. Evidence remains in resident log
1544. No full rebuild, export or installed checker change was needed.

These are semantic composition interfaces. Native referenced-module receipts,
checked initialization of the actual-return predicates, concrete finite-input
invariants and structural residual discharge are still needed for numbervars.pl.
There is no new benchmark verdict; priority 1 remains active.


Native inspection 2678 confirms two recursive Split sites and two univ operations
in the original numbervars graph. `LP_Prolog_Finite_Fresh_Body.thy` now checks that
fresh decomposition is the first source-clause operation, with distinct body-only
outputs and an input occurring in the head. The matching native receipt binds the
entire original clause and its index. Entry freshness cannot be reused after an
intervening unification. Check 1912 verifies this interface and rejection lemmas.

Check 1913 (1.922 seconds) proves the combined finite-continuation rule: given the
checked clause, actual MGU resolution, a finite instantiated head, a constructor
input and the actual successful univ outcome, finite continuation goals remain
finite. Input finiteness is derived from the instantiated head. This does not
assume that arbitrary resolution preserves finite heads; establishing that
premise at every recursive entry remains necessary. The dependency audit passes
without oracles or skipped proofs. Evidence remains in resident log 1544.

Ferrum native 2679 passes three focused tests and an original-source diagnostic:
the relevant clause has fresh-decomposition evidence, both univ views initialize,
and all 69 established states project. Renamed fixtures, head/output aliases,
changed source clauses and intervening unification are covered. No executable
source certificate or benchmark verdict is added by these candidate receipts.


`LP_Prolog_Finite_Ground_Binding.thy` supplies the finite-input equality case
needed alongside fresh univ decomposition. Its general theorem proves that an
actual most-general unifier of a finite term with a ground constructor tree
preserves finite continuation goals. The proof constructs a finite comparison
substitution from the actual unifier on variables of the input, using identity
elsewhere; it does not assume the actual substitution is globally finite.
A checked symbolic form derives right-side groundness from the incoming ground
set. A separate free-variable specialization does not require input finiteness.

Check 1920 verifies the general and specialized rules and the no-oracle/no-skip
audit in 0.717 seconds. Rejection controls cover missing groundness and freeness
for the specialization. Attempts 1914 and 1918 corrected proof-name collisions;
1916 corrected subset syntax. Intermediate checks 1915, 1917 and 1919 passed.
Evidence remains in resident log 1544; no checker export or full rebuild ran.

Native evidence 2680 found that the established projected equality states do not
carry freeness. This motivated the proved general finite-input rule rather than
adding an unchecked free fact. Native 2681 finds conditional ground-equality
receipts at nodes 12, 19 and 67. Node 60 lacks right-side groundness, and nodes 10
and 58 require their existing functor projection. The next concrete gap is the
helper counter's conditional ground-return fact across the recursive Split.
All 69 states still project; no root certificate or new verdict is claimed.


The shared guarded ground-return theorem is now parameterized over builtin and
domain interpretations, with explicit successful-builtin coverage, control-outcome
exclusions, substitution stability and ground-evaluation premises. Its previous
finite-source theorem remains an unchanged compatibility corollary. Check 1921
passes this refactoring and dependency audit in 2.172 seconds.

`LP_Prolog_Univ_Ground_Return.thy` discharges those premises for the extended univ
interpretation. Existing unconditional builtin success clauses cover actual univ
returns; the actual source execution still checks decomposition and all outcomes.
The proof reuses the same source-clause cover, guarded ground-mode checker and
scoped actual-answer theorem. It does not introduce another operational model or
assume integer counters. Missing reachable univ clauses are explicitly rejected.
Check 1923 passes the source bridge, compatibility dependencies and rejection
lemma in 7.502 seconds (composition alone passed 1922 in 3.198 seconds).
Evidence remains in resident log 1544; only affected theories were reloaded.

Native inventory 2682 confirms the existing return inference already proves
numvars' conditional counter-groundness: Split 30's ground V1 gives ground V2;
Split 44's empty input ground set yields no such fact, while ground V1 again
gives ground V2. This is a context-transport gap, not missing ground-mode search.
Native regression 2683 passes a renamed recursive functor/counter example,
missing-input and removed-output-contract controls, and refuses to infer tree
output groundness from the model's erased source equality. Actual module-return
interface transport and finite recursive-entry invariants still need assembly.
No root verdict, native certificate, checker export or full rebuild is claimed.


`LP_Prolog_Univ_Ground_Receipt.thy` now connects the existing checked ground-return
receipt to the actual Split interface under extended univ semantics. Generic
reinterface reflection identifies a source valuation for the returned tuple.
The receipt theorem preserves the incoming full stable context and functor facts,
then adds only ground outputs justified by the actual-return model. It reuses
`lpp_finite_ground_receipt_check`; no independent summary checker is introduced.
Check 1925 passes all three theorems and the dependency audit in 5.868 seconds.
Attempt 1924 corrected an unavailable legacy-envelope lemma by deriving incoming
groundness directly from the stable evaluation interpretation; no integer
compatibility assumption is needed for that derivation.

Check 1926 extends the finite ground-equality theorem to explicit incoming
context observations (2.051 seconds, no-oracle/no-skip audit). Native 2686 binds
that context in the receipt instead of mutating the graph ground set. Missing
context and changed saved-answer controls pass. Original-source diagnostics now
cover both marker-binding branches, at region 0/local 12 and region 47/local 12,
as well as their ground arithmetic equalities.

Context inventory 2685 corrected the prior raw-node diagnosis: the established
context fixed point already transports counter groundness through both Splits.
The old diagnostic 2684 failed before inference because it requested legacy
residual projection. It now uses the same routing plan's path starts, without
changing production projection or certification. Both Split prefixes receive
ground V1 and return ground V2. Finite-entry/spine invariants, complete module
serialization, structural residual proof and strict replay remain outstanding.
No benchmark verdict, installed checker change or full rebuild is claimed.


`LP_Prolog_Functor_Spine_Return.thy` connects successful univ decomposition to
exact argument-list length and lifts that observation through actual helper
returns for arbitrary source templates. It reuses the existing list-length
relation and generic substitution/actual-answer theorem. A nonempty list's
returned tail retains its predecessor length, supplying strict spine descent.
Every incoming frame must initialize the observation. The proof neither assumes
helper termination nor infers finite elements from a finite spine.

Check 1927 passes four theorems and the inherited-oracle/no-skip audit in 0.911
seconds, including a cyclic-element control that has a finite spine but no finite
tree. Resident log 1544 retains the evidence. SWI control 2687 independently
confirms that binding an element cyclically preserves a two-cell list spine,
while a cyclic spine is not a proper list. This is semantic control evidence,
not a benchmark termination result.

The remaining recursive-child argument must still establish finite term entries
and relate constructor traversal to the structural residual. Spine descent alone
covers the tail continuation, not recursion into each element. Complete native
module/context serialization and residual certification remain open; no installed
checker or root verdict changed and no rebuild was needed.

`LP_Prolog_Finite_Matching_Head.thy` proves finite instantiated heads, bodies,
and caller continuations for actual MGU resolution when the selected call is
an instance of the clause head. The executable premise reuses the existing
`lp_cut_check_match`, including distinct binding keys and exact one-pass head
substitution. It requires finite input and continuation; it does not infer
finiteness from matching. A constructor-with-nonground-elements positive control
and a repeated-head alias rejection are included.

Resident checks 1928/1929 passed the semantic and executable bridges. Check 1930
failed to instantiate an existential factorization in the proof; 1931 makes the
identity comparison explicit and passes. Final 1932 checks all five theorems and
the no-oracle/no-skip audit in 0.767 seconds. No shared theory or installed checker
was rebuilt. Log 1544 retains the attempts.

Native inventory 2688 on the original established contextual graph reports six
matching variable-head states and six unmatched list-head states. List calls
remain abstract at those nodes; their retained constructor/spine observations
must justify runtime matching or the existing ground-anchor rule. Syntactic
matching alone does not close these cases. Initial native compilation used the
wrong enum variant in diagnostic code; the corrected incremental build passes
and the exact ignored diagnostic passes. Source proof assembly, recursive finite
entries, residual discharge, and strict replay remain open. No new root verdict
is claimed.

`LP_Prolog_Finite_List_Head.thy` connects an incoming proper-spine observation to
actual successful clause resolution. Constructor discrimination exposes the
nonempty list; a linear cons head with arbitrary additional variable arguments
then matches the runtime call. The matching-head theorem supplies finite
instantiated head, body, and continuation under explicit finite-input premises.
A separate theorem transports the exact predecessor spine length to the head's
tail variable. It needs neither ground elements nor a helper termination premise.

Resident 1933 passes the shape and finite-resolution theorems in 1.625 seconds;
1934 also passes tail observation and the no-oracle/no-skip audit in 1.760 seconds.
Native 2689 discovers all twelve contextual selected-clause candidates on the
original established graph: six Matching, four GroundAnchored, two ObservedSpine.
The latter remain explicit obligations, not assumed facts. Receipts bind the
entire source state, context, selected index and clause. Mutations cover missing
context, clause changes, return-interface changes, repeated variables, and
replacement of the spine obligation by a ground claim. SWI independently shows
that dropping the linear-head restriction can turn a finite one-cell list into
a cyclic term. Complete module-level invariant transport, source assembly and
residual certification are still required; the installed checker and root totals
are unchanged.

`LP_Prolog_Spine_Context.thy` provides a checked frame-local proper-spine context:
existing facts, argument lists from functor observations, cons tails, nil, and
cons construction from an established tail. Runtime substitution and exact
one-pass interface transport are proved. Actual successful helper returns
preserve the context only when every incoming frame initializes it; the proof
does not leak active observations into saved alternatives or infer finite trees.
Missing acquisition facts, tail facts and interface facts are rejected.

Attempts 1935–1941 exposed local proof-development errors (constant/command name
collisions, existential witnesses, and case instantiation); all remain in resident
log 1544. The explicit case proof passes in 1942. Final 1943 also checks the
actual-return interface corollary and rejection controls in 7.558 seconds with
the inherited-oracle/no-skip audit. No full build or checker export ran.

Native 2690 adds corresponding derivation/transport discovery and includes an
argument-spine receipt in the existing initialized univ view. Focused tests pass
(one spine-context test; three univ tests) including missing facts, wrong
interfaces, unproved tails, and saved-frame reuse. The original root diagnostic
finds both univ acquisitions with argument-spine evidence, still 69 projected
states, zero open projections, and two frame-local functor relations. This is
conditional acquisition evidence. Complete module context reconstruction and
source/residual assembly remain open; no benchmark verdict changed.

`LP_Prolog_Spine_Shape.thy` identifies proper-spine observations exactly with the
existing one-node return grammar (nil, or cons with Any element and recursive
tail). It supplies functor-acquisition and actual-return corollaries in the
shared return-shape representation; no separate context/state format is needed.
The Any field still admits rational elements. Checks 1944–1947 corrected list
case/induction proof scripting; 1948 passes equivalence. Attempt 1949 needed
explicit pointwise list predicates. Final 1950 passes all three exported lemmas
and the inherited-oracle/no-skip audit in 1.650 seconds, in resident log 1544.

Native 2691 reuses shape histories and the existing contextual region builder.
A descending candidate-interface analysis checks every established incoming
boundary and both Split routes, preserving incoming spine facts across actual
helper-return interfaces rather than inferring new facts from termination.
The first inventory lost all acquisitions because univ receipt discovery ran
after ordinary history annotation had changed its exact successor. Discovery
now precedes annotation; the original graph is unchanged. Corrected inventory
retains tail V3 at both Split entries 30/44 and list V0 at module 35; both
previously unsupported list-head states are supported. Module root 0 has no
assumed spine facts. The renamed recursive fixture passes, while removing the
univ acquisition removes the inferred spine interfaces and head support. All
nine existing context/backtracking tests pass. These are candidate reconstructions:
full source-table checking, finite-entry invariant assembly, structural residual
discharge and strict root replay remain outstanding. No installed checker change
or benchmark gain is claimed.

Finite continuation assembly exposed a concrete limitation of standalone prefix
answers. `LP_Prolog_Finite_Return_Control` proves that resolving a ground fact
with an empty continuation admits an arbitrary substitution on an unobserved
captured slot under the existing MGU relation, including a cyclic image of a
finite variable. This is an over-approximation in the proof semantics, not a
claim that SWI creates such a binding. The positive control proves that an
occurrence in the attached finite continuation prevents this change. The source
semantics and every established construction rule remain unchanged.

`LP_Scoped_Answer_Invariant_Composition` extends shared LP-with-cut composition:
an invariant is initialized at the prefix state, preserved by actual attached
steps at reachable prefix states, and retained when a completed prefix frame is
removed. The continuation receives that invariant alongside its actual prefix
answer. Specializing the invariant to True recovers unrestricted composition.
`LP_Prolog_Domain_Invariant_Composition` instantiates the same theorem for the
existing builtin/domain answer semantics. `LP_Prolog_Finite_Continuation_Composition`
extracts finite continuation goals from a finite attached execution, retaining
an explicit preservation premise. `LP_Prolog_Functor_Split_Invariant` applies this
to the existing checked Split shape, routes and return projection. Standalone
actual-return contracts remain separate; no finite return claim is assumed.

Resident checks: 1951–1953 corrected explicit MGU/transition instantiation;
1954 passes the initial counterexample. 1955 passes generic composition; 1956
needed explicit I/rest instantiation; 1957 passes the domain instance and cyclic
control. 1958 passes finite-continuation specialization; 1959 adds reachable-state
preservation and the True compatibility specialization (final finite theory
2.247 seconds). 1960 was interrupted after 30.890 seconds: a newly quantified
saved-tail variable shadowed the fixed interface variable list. Renaming it and
making composition premises explicit fixed the statement; 1961 corrected quoted
term syntax and 1962 passes the Split theorem in 2.287 seconds. Attempts 1963–1965
needed explicit list-membership introduction; final counterexample/positive
control 1966 passes four theorems in 0.334 seconds. All dependency audits pass,
with inherited checker oracles only for the functor Split theorem. All attempts
remain in resident log 1544. No native build or checker export was necessary.
The root still requires discharge of the reachable invariant-preservation premise,
complete native source assembly, structural residual certification and replay.

Finite attached-execution preservation (resident checks 1967–1973) now covers
complete states, including saved alternatives, scope transport and pruning.
`LP_Prolog_Finite_Execution_Step` proves resolution from finite instantiated
heads and equality from ground right-hand sides; dynamic meta calls remain an
explicit separate obligation. `LP_Prolog_Finite_Execution_Builtin` lifts checked
outcome finiteness to extended and domain answer steps, retaining failure/error
branches. `LP_Prolog_Finite_Operation_Outcome` supplies arithmetic, term tests,
and fresh univ outcomes, including the actual fresh-clause resolution rule.
These are finiteness results, not termination or builtin-domain coverage.
Arithmetic uses the existing stable source interpretation, without equating
groundness with integer inputs. The domain-error self-loop can preserve
finiteness and still diverge.

Attempt 1967 needed explicit extraction of the actual MGU premise; 1968 passes
base preservation. Attempt 1969 required explicit builtin cases; 1970 passes.
Attempt 1971 passes initial operation instances. Attempt 1972 required explicit
scope/entry cases; final 1973 rechecks all three theories and passes the final
operation theory in 2.773 seconds. Dependency audits reject skipped proofs and
oracles. All attempts remain in `target/prolog-domain-graph-resident-1544.log`.
No unified checker export or new certified benchmark is claimed. Reachable
node coverage, source assembly, residual certification and replay remain open.

Finite functor table specialization (resident checks 1974–1977):
`LP_Prolog_Finite_Functor_Normalization` discharges the finite-execution
normalization premises for arithmetic `is` and constructor-view `=..`, retaining
the complete saved stack. These are pre-unification normalization results;
subsequent equalities still require their own checked contracts. Both results
are instantiated into the existing functor node contracts. The finite table
specialization also discharges scope equivariance using the checked scope-word
preservation theorem. It retains complete local/boundary coverage, source
program checks, initialized knowledge/context/functor facts and residual SN.

Check 1974 passes both normalization lemmas in 1.661 seconds. Attempt 1975 needed
explicit rewriting of the node-state shape before instantiation; 1976 passes
both node instances in 2.463 seconds. Final 1977 checks the table specialization
and all dependency audits in 2.472 seconds. Normalization lemmas have no oracles;
node/table contracts inherit only the existing checker dependencies. Evidence
remains in resident log 1544. No native or unified checker rebuild was needed.
This does not yet assemble or certify a source root. Next Isabelle 1978.

Runtime support separation (resident 1978–1981): inspection of the established
synthetic univ equality shows that finite execution, distinct free outputs and a
proper argument spine are insufficient alone. An output can occur inside a list
element. `LP_Prolog_Separation_Context` represents disjoint runtime supports as
explicit two-term facts, proves exact interface transport and acquires the facts
from the checked fresh-clause MGU. Its consumer combines those facts with free
outputs to establish finite continuation after actual univ decomposition.
Separation is deliberately not declared stable under arbitrary substitutions.
Checked controls show arbitrary substitution can destroy it and free outputs
can coexist with a finite input that contains one of those outputs.

Attempt 1978 collided with the existing `fact` constant; renaming the binder
fixes it and 1979 passes acquisition/transport/controls in 5.482 seconds.
Attempt 1980 used reserved `values` as a fact label; renaming it fixes the
consumer proof. Final 1981 passes the complete theory and no-oracle/no-skip
dependency audit in 6.045 seconds, retained in resident log 1544. This is not
blanket runtime-substitution transport. Carrying the facts through synthetic
normalization links and integrating complete source assembly remain required.
No checker export or certified benchmark change. Next Isabelle 1982.

Reflexive normalization transport (resident 1982–1993):
`LP_Prolog_Separation_Reflexive` proves support separation survives an actual
reflexive MGU on finite terms present in the continuation. Most-generality
provides a shared inverse on those terms; a finite inverse implies that variable
images remain variables, with distinct original variables having distinct
images. Companion lemmas prove finite continuation and free-knowledge transport
for explicitly covered variables. This does not apply to arbitrary substitutions
or captured variables absent from the continuation.

Attempts 1982–1983 corrected the finite-term induction case name; 1984–1988
made map identity, child induction and existential reasoning explicit. 1989
passes separation (0.522 seconds); 1990 adds finite continuation and inverse
variable images (0.635 seconds). Attempt 1991 was interrupted after 18.508 seconds
in broad membership search; 1992 showed the needed explicit subset elimination.
Final 1993 uses that elimination and passes all six dependency-audited lemmas
in 0.842 seconds, without oracles or skipped proofs. All attempts remain in
resident log 1544. No native/checker rebuild, source acceptance or root gain.
Next instantiate these rules on the paired normalized univ equalities and
thread the facts through source table links. Next Isabelle 1994, native 2694.

Paired normalized univ equalities (resident 1994–1998):
`LP_Prolog_Finite_Pair_Unify` proves finite continuation after a binary constructor
pair MGU with distinct fresh variables and separated finite right-hand terms.
It then composes an actual reflexive MGU with that pair MGU, using the checked
inverse-based finiteness, freeness and support transport. The final theorem
instantiates the sequence to the two normalized univ equalities, retaining the
constructor name, actual argument list and both substitutions. This supplies
the full successful-sequence finite premise without assuming arbitrary
substitution stability; source failure/error coverage remains separate.

Check 1994 passes the general pair rule in 0.331 seconds. Attempts 1995–1996
needed explicit fixes for colliding constants and defined terms; 1997 passes
the composed rule in 0.691 seconds. Final 1998 passes the actual univ sequence
and no-oracle/no-skip audits in 0.923 seconds. Resident log 1544 retains all
attempts. No checker rebuild or accepted root certificate. Next Isabelle 1999.


Functor control reductions and finite action coverage (resident 1999–2004):
The established projected numbervars tables contain four TrimBarriers and four
StackSplit operations. `LP_Prolog_Functor_Control_Check` now represents them as
LPPFTrim and LPPFParallel, requiring the exact barrier suffix or complete
alternative/link/type-list coverage and a checked stable functor link for each
child. These constructors do not classify a boundary as solved.
`LP_Prolog_Functor_Control_Reductions` proves their node answer contracts using
the shared domain barrier/singleton composition rules and an explicit deletion
closure premise for the invariant. Residual paths are lifted from each child to
the original residual subject. Missing alternative/context coverage and a
nonbarrier suffix are rejected by proved controls.

Resident 1999 rejected missing whitespace in the subset premise; 2000 verifies
the reduction theory in 3.000 seconds. Finite-execution instances are integrated
in `LP_Prolog_Finite_Functor_Normalization`. Resident 2001 verifies these and
reloads the existing Split invariant theorem (5.564 seconds for the latter).
`LP_Prolog_Functor_Simple_Control` supplies a syntactic simple-frame check and
finite node contracts for ordinary allocation/administrative operations and
term tests. It explicitly rejects clause resolution, equality and meta calls;
these retain separate finite-unification obligations. The initial evaluation
proof in 2002 needed function induction rather than an ineffective splitter;
2003 passes in 2.962 seconds, and 2004 including term-test contracts passes in
3.536 seconds. All new theorem dependency audits pass, with no skipped proofs
or additional oracles beyond the existing checker dependency allowance.

Evidence: `target/prolog-functor-control-2004-resident.log`, with all attempts
also retained in `target/prolog-domain-graph-resident-1544.log`. Only affected
theories were reloaded in the resident Isabelle process. No unified executable
was rebuilt or exported, and no new root was accepted. Source serialization,
resolution/equality invariant coverage and referenced Split assembly remain.
Next Isabelle 2005; priority 1 remains active.


Context-qualified finite unification contracts (resident 2005–2007):
`LP_Prolog_Functor_Finite_Unification` adds a node-contract lifting rule whose
finite-preservation premise can use that node's incoming ground/free/context
and functor knowledge. This avoids demanding an unconditional invariant when a
local ground-side premise is known only from a checked helper return. It proves
full-state ground-equality and matching-head resolution preservation and lifts
both to the stable functor node answer contract. Ground equality uses the union
of state groundness and checked source-context groundness; it makes no integer
assumption. Saved alternatives remain part of the full state.

Resident 2005 found a missing import for the context groundness theorem. After
adding the existing Stable_Builtins dependency, 2006 exposed an inappropriate
unfolding of the generated function definition for no-builtin frames. Using the
function's simplification equations fixes that proof. Resident 2007 passes in
4.238 seconds, including the dependency audit (no skips or added oracles).
Evidence: `target/prolog-functor-finite-unification-2007-resident.log`; all attempts
remain in `target/prolog-domain-graph-resident-1544.log`. Only affected resident
theories were loaded. No checker export/rebuild or accepted benchmark gain.
Remaining cases include ground-anchored/list-spine heads and normalized univ
reflexive/separated equalities, as well as full source/Split assembly.
Next Isabelle 2008.


Univ initialization equation in checked successor contexts (resident 2008–2013):
`lpp_check_univ_evaluation_context` now constructs the successor's available
context by adding exactly (input_template, Var value_variable) to the incoming
context. Both evaluation and stable source contract proofs justify this equation
using the fourth conclusion of the existing initialization theorem, before using
the shared checked functor link. Freshness and saved-state preservation remain
unchanged. No arbitrary certificate-supplied equality is accepted by this rule.

Resident 2008 exposed the missing Equation_Initialization import; 2009 loads the
corrected checker and all affected dependencies through finite-unification node
contracts successfully. `LP_Prolog_Functor_Reflexive_Contract` then proves full-state
finite preservation for an actually reflexive MGU and lifts a checked incoming
context equation to the functor node contract. An equation-availability lemma
connects the exact univ extension to that check; a missing nontrivial equation is
rejected. The initial 2010 proof needed explicit stable evaluation/SP parameters;
2011 hit a reserved context identifier; 2012 needed a term-constructor split in
the availability lemma. Final 2013 passes in 6.606 seconds, including dependency
audits with no skipped proofs or additional oracles. The existing Split invariant
also rechecks (3.475 seconds in the 2010 load).

Evidence: `target/prolog-univ-context-reflexive-2013-resident.log`, with all attempts
in `target/prolog-domain-graph-resident-1544.log`. Only affected theories were
reloaded in the resident process. No native rebuild, unified export, or benchmark
verdict change. Next connect the separated pair-equality and remaining head
contracts, materialize the refined native equation contexts in source assembly,
and complete referenced Split assembly and residual discharge. Next Isabelle
2014; priority 1 remains active.


Ground-anchored and observed-spine node contracts (resident 2014–2015):
`LP_Prolog_Functor_Anchored_Contract` lifts the existing anchored-head theorem
through complete source steps to the finite functor node contract. It explicitly
checks the selected source head, arity and variable coverage, and allows ground
inputs justified by the current source context. The repeated-head example passes;
removing its ground premise is rejected. No integer typing is inferred.
Resident 2014 passes in 2.269 seconds.

`LP_Prolog_Functor_Spine_Head_Contract` performs the corresponding lift for a
linear cons head using the existing proper-spine shape grammar. The checked
context must contain the exact argument shape observation. Finite execution,
distinct head variables and arity remain separate premises; proper spines do not
prove finite elements. Saved alternatives remain part of the full state.
Resident 2015 passes in 5.796 seconds, including the missing-observation control
and dependency audit. No skipped proofs or added oracles. These provide the two
remaining head-contract families found in the original projected numbervars
inventory; they do not themselves assemble a root certificate.

Evidence: `target/prolog-functor-head-contracts-2015-resident.log`; all attempts
remain in `target/prolog-domain-graph-resident-1544.log`. Only required resident
theories were loaded. No checker executable rebuild/export or benchmark gain.
Next address explicit separation acquisition/transport for the normalized pair
equalities and finish source serialization, referenced Split assembly and
residual proofs. Next Isabelle 2016; priority 1 remains active.


Univ separation transport and complete pair steps (resident 2016):
`LP_Prolog_Separation_Univ_Transport` proves equality of runtime-variable support
between a constructor value and its observed argument list. With the actual
initialization equation and the two acquired input/output separation facts, it
establishes separation of the normalized requested/observed pair. This uses the
actual observation, not injectivity of constructor names or syntactic freeness.
It then lifts reflexive-MGU separation preservation to symbolic context terms,
requiring that both terms occur in the actual continuation. Finally it lifts the
separated-pair finite-goals theorem to complete source states, retaining saved
alternatives. All finite, distinctness and runtime-support premises remain.

Resident 2016 passes in 4.325 seconds with no skipped proofs or oracles. Evidence:
`target/prolog-univ-separation-2016-resident.log`, also retained in the full
resident log. No executable export/rebuild. Native 2702 reconstructs both actual
fresh-resolution/univ/reflexive/pair paths and checks that the three intermediate
nodes have only their expected incoming local edge and are not module boundaries.
This is not yet acceptance of a source root. Next integrate these separation
premises into the checked local-table representation and complete source/Split
assembly and residual discharge. Separation must never use the generic
substitution-stability rule for ordinary functor facts. Next Isabelle 2017;
priority 1 remains active.


## Node-local separation table composition (resident 2017–2018)

`LP_Prolog_Functor_Premised_Table` extends the existing functor table contract
with conditions indexed by node and valuation. Shared `lp_answer_contract_modular`
still performs assembly; root conditions and every child condition remain explicit
obligations. Scope restoration uses the same valuation witness as state, context
and residual representation. The True specialization is proved equal to the
previous representation, module interface and node contract. False premises exclude
representation; a missing separation-context entry is rejected, not interpreted
as an empty context. No substitution stability is assumed for separation.

`LP_Prolog_Separation_Functor_Link` combines ordinary checked links with exact
separation transport under the same interface substitution. Its witness theorem
establishes both sets of facts for one target valuation, rather than joining
unrelated existential witnesses. Resident 2017 passes in 4.373 seconds and 2018
in 2.837 seconds, with strict zero-oracle/zero-skip checks. Existing Split invariant
and spine-head contracts load successfully. Evidence, including earlier rejected
2017 attempts (ambiguous instantiation and reserved/global identifiers), is retained
in `target/prolog-domain-graph-resident-1544.log`; the final checked loads are also
in `target/prolog-premised-table-2017-2018-resident.log`.

Ferrum 2703 binds these node contexts to both complete acquisition traces and the
refined residual table. This remains unexported producer/theory work: no accepting
source constructor, executable regeneration or new benchmark certificate. Next
instantiate local action contracts with these separation-aware link obligations,
then finish referenced Split/return assembly and residual discharge. Next resident
number: 2019. Priority 1 and numbervars remain unfinished.


## Separation-aware equality actions and finite pair contracts (2019–2021)

`LP_Prolog_Separation_Equality_Action` proves the existing equality action with
node-local separation conditions. Success uses the actual MGU and resolution
environment; failure separately transports only incoming facts. Both links retain
ordinary contexts, functor observations, freeness choices and residual subjects.
`LP_Prolog_Separation_Equality_Contract` integrates this into the premised node
contract with actual-return behavior and the runtime invariant intact.

`LP_Prolog_Separation_Pair_Control` adds an executable side-condition check for
matching binary constructors with two distinct free variables and an explicit
support-separation fact. It proves full-state finite preservation for the actual
transition and instantiates the separation-aware node contract. Missing separation
and repeated variables are rejected. This does not assume arbitrary unification
preserves finiteness or infer separation from freeness.

Resident checks pass with zero oracles/skips: 2019 in 2.572 seconds, 2020 in 1.047
seconds, 2021 in 2.453 seconds. All attempts, including corrected type instantiation
and proof-tactic failures, are retained in
`target/prolog-separation-equality-2019-2021-resident.log`. Native 2704 reconstructs
all seven local equality actions and their 14 alternatives. The two equality-shaped
module boundaries remain explicit obligations. No checker export or new certified
root. Next connect reflexive separation preservation to the refreshed normalized
valuation, and add the analogous fresh-resolution/univ action contracts. Then
complete source/module assembly and residual discharge. Next resident 2022.


## Checked continuation separation through reflexive normalization (2022–2023)

`LP_Prolog_Separation_Refresh` checks that both sides of every retained separation
fact occur in the actual continuation and satisfy the namespace bound. The proof
uses actual reflexive-MGU continuation factorization, then translates preservation
into `lp_cut_resolution_env` through the existing refresh theorem. It does not
assert arbitrary substitution stability. Positive pair coverage and negative
missing-continuation/unobserved-term checks are included.

`LP_Prolog_Separation_Reflexive_Contract` now discharges the former semantic
success-preservation premise using checked conditions: context equation, continuation
coverage, incoming fact inclusion, namespace bounds and separate branch transports.
It also proves the full-state finite invariant through the actual reflexive step.
The final resident load reaches `SEPARATION_REFLEXIVE_FINAL_2022_2023_OK` with strict
zero-oracle/zero-skip checks. All attempts are retained in
`target/prolog-separation-refresh-2022-2023-resident.log`, including an interrupted
28-second broad proof search and corrected explicit instantiations.

Ferrum 2705 confirms normalization leaves the relevant refreshed separation terms
unchanged on both original numbervars paths. The receipt records these terms and
checks that equality explicitly; a changed term requires a future equation-rewrite
proof rather than inheriting this rule. All five tables still reconstruct. No
export, source certificate or root gain. Next fresh-resolution acquisition and
univ initialization action contracts, then complete source/module assembly,
residual discharge and strict certified replay. Next resident 2024.


## Resolution separation and fresh matching clause contracts (2024–2027)

The separation-aware resolution action and node contract retain the existing
checked source operation, contexts, saved alternatives, return interface and
strict residual links. Success uses the actual clause MGU; failure uses its
original valuation and a separate separation transport obligation.

Fresh-univ acquisition now transports clause-local separation into the actual
resolution environment. The matching-head instance theorem proves the instantiated
call finite, and the fresh matching node contract derives both acquisition and
full-state finite preservation from these checked conditions. No unconditional
freeness-to-separation inference is introduced. Resident 2024–2027 reach their OK
markers with strict zero-oracle/zero-skip checks. All attempts, including corrected
proof instantiation and the reserved `instance` identifier, are retained in
`target/prolog-separation-resolution-2024-2027-resident.log`.

Native 2706 reconstructs all eight actual resolution actions and twelve branches,
including the two fresh acquisition sites. An initial inventory mistakenly included
four stack-split actions because they had clause-shaped states; the action receipt
now requires actual `SymbolicAction::Clause`. Earlier and corrected attempts are
retained. This remains unexported work, not a source certificate or root gain.
Next bind clause-prefixed acquired facts to normalized source facts, integrate
univ initialization contracts, then complete source/module assembly, structural
residual discharge and strict certified replay. Next resident 2028.


## Normalized fresh-clause separation (2028–2029)

`LP_Prolog_Separation_Normalize` reuses the verified cut equation normalizer on
separation payloads. Its soundness theorem requires the initialized source
equations and preserves evaluated separation facts. Encoded equality goals are
payloads, not executed unifications. `LP_Prolog_Separation_Normalized_Fresh`
instantiates the fresh matching node contract with normalized facts: actual MGU,
namespace bounds and source knowledge establish the resolution equations, and
checked normalization connects clause-prefixed acquisition to the successor facts.

Resident 2028 passes in 1.178 seconds and 2029 in 0.585 seconds with strict
zero-oracle/zero-skip checks. Evidence:
`target/prolog-separation-normalize-2028-2029-resident.log`. Ferrum 2707 binds
clause-prefixed facts, actual resolution equations and normalized successor facts
in the acquisition receipt. Both original numbervars paths and all five tables
reconstruct; removing initialization or clause facts is rejected by reconstruction.
No new checker export or benchmark certificate. Next integrate univ initialization
with separation-aware node conditions, then complete source/module assembly,
residual discharge and strict certified replay. Next resident 2030.


## Univ initialization in separation-aware node contracts (2030–2033)

`LP_Prolog_Univ_Separation_Context` extends the existing normalized univ return
contract with separation transport. Ordinary context/functor facts and separation
use one checked target valuation. `LP_Prolog_Univ_Separation_Initialization` proves
pair separation from the incoming input/output separation facts, preserving the
original evaluated state under fresh observation initialization.

The control and node contract theories integrate this into the premised table
interface. The finite node theorem discharges initialization and finite normalized
execution from checked source-action conditions and incoming fact inclusion; it
does not assume the initialized separation conclusion. Existing univ domain,
error/return behavior and shared normalized answer composition remain in use.
Resident 2030–2033 pass in 1.430, 0.293, 5.236 and 0.892 seconds, with zero
oracles/skips. All attempts, including corrected type annotations and theorem
instantiations, are retained in `target/prolog-univ-separation-2030-2033-resident.log`.

Ferrum 2708 binds both original univ nodes and their four alternatives. Only the
initialized successor carries its acquired pair fact. Missing initialization,
branch, trace and facts are rejected by reconstruction. No checker export or
new certified root. Next assemble action coverage for the premised table, including
ordinary actions with empty successor separation contexts and explicit Split
boundaries; then finish source constructor, residual discharge and strict replay.
Next resident 2034.


## Complete native obligation coverage and ordinary empty-condition links (2034–2035)

Ferrum 2709 reconstructs a row for each local state, distinguishing boundaries,
exhaustion, equality, resolution, univ and ordinary actions. Ordinary rows require
explicit empty separation contexts at all successors; every existing source
context, observation and interface is retained. Boundaries remain obligations,
not proofs. The five original tables cover 68 states: 7 boundaries, 23 exhausted,
7 equality, 8 resolution, 2 univ and 21 ordinary rows.

`LP_Prolog_Separation_Empty_Actions` proves the empty-separation specialization of
the existing checked link and uses it for administrative, clause-selection and
meta-call steps. `LP_Prolog_Separation_Empty_Test` covers every admitted term-test
outcome with its own checked target. Resident 2034/2035 pass in 0.850/0.500 seconds
without skips or oracles. Evidence:
`target/prolog-separation-empty-2034-2035-resident.log`.

This is complete native receipt coverage, not a completed source proof. Ordinary
node-contract assembly, trim/parallel and arithmetic normalization integration,
explicit Split contracts and the accepting source constructor remain. Structural
residual discharge and strict replay are still required; no export or gain is
claimed. Next resident 2036.

## Checked ordinary actions in premised tables (2036–2042)

`LP_Prolog_Premised_Base_Contract` assembles actual base-semantics steps into
node contracts, retaining represented strict successors, actual return coverage
and the runtime invariant. Its exhausted-state instance requires a literal empty
state; it does not discharge module boundaries. Administrative and clause-selection
instances preserve finite execution. Trim and parallel instances retain barrier
checks and every alternative through the existing source-action checker.

The builtin instances cover every admitted term-test outcome and existing observed
arithmetic normalization. Arithmetic keeps the existing source domain and scalar
evaluation, including error and binary64 behavior; no integer-only replacement is
introduced. The additional separation conditions must be proved empty at each
used target. Ordinary contexts, equations, functor facts and return observations
remain checked in the same target valuation.

`LP_Prolog_Separation_Ordinary_Check` now gives an executable additional side
check and a sound finite node-contract dispatcher for these ordinary actions.
Its term-test instance conservatively checks both targets, including any branch
that an earlier source check might exclude. Equality, resolution, univ and
module boundaries retain their dedicated obligations. This additional check alone
is not a source-action certificate. Twelve generalized positive/rejection lemmas
cover missing contexts, undischarged facts, missing failure targets/alternatives,
nonempty terminal states, wrong test arity/arithmetic name and retained specialized
obligations.

Final resident loads take 0.465/1.993 seconds (base/simple), 2.062 (reductions),
4.070 (builtin contracts), 1.468 (finite instances), 3.530 (dispatcher) and 0.336
(regressions). All new checked theorem groups have zero oracles and skips.
`target/prolog-separation-ordinary-2036-2042-resident.log` retains successful loads
and failed/corrected attempts, including interrupted broad proof searches.
No native rebuild, full Isabelle rebuild, checker export or benchmark gain.

Remaining work: discharge the finite matching, anchored and observed-spine
resolution instances and ground equality under premised tables; assemble these
with the existing fresh/reflexive/pair/univ contracts into the complete executable
local checker. Then bind the source constructor and explicit Split return/module
dependencies, discharge structural residuals and run strict source-certified
replay. The full campaign remains 90 YES + 97 NO; numbervars is still UNKNOWN.
Next native 2710, resident 2043.

## Finite unification in premised tables (2043–2044)

The empty-successor specialization now covers equality and resolution, checking
both admitted outcomes independently. Incoming node conditions are preserved as
local premises; neither branch receives invented separation facts. Finite instances
reuse the established proofs for ground equality, matching heads, ground-anchored
heads and observed proper-spine heads. Groundness may come from the checked source
context and does not imply integer typing. A proper spine alone is insufficient:
finite runtime execution remains a separate premise, and the head must be linear.

`LP_Prolog_Separation_Empty_Unification` and
`LP_Prolog_Separation_Finite_Unification` pass resident 2043/2044 in 5.577/0.895
seconds with zero oracles/skips. Evidence:
`target/prolog-separation-unification-2043-2044-resident.log`. No native rebuild,
export or new certified root. Next combine these instances and the existing
fresh/reflexive/pair/univ rules in the executable local checker, then bind source
and Split/module assembly, residual proofs and strict replay. Next resident 2045;
native remains 2710.

## Executable separation action and table assembly (2045–2053)

The new head check binds matching, ground-anchored and observed-spine receipts to
the actual selected call and source clause. The unification dispatcher retains
both admitted outcomes and checks their successor conditions. Dedicated executable
side checks cover separated pairs, context-reflexive equality, normalized fresh
clause acquisition and initialized univ observations. These checks reuse the
established semantic proofs and all ordinary source-action checks.

`LP_Prolog_Separation_Action_Check` dispatches these rule families from explicit
local evidence. `LP_Prolog_Separation_Table_Check` checks witness and separation
coverage for every source row, then derives local answer contracts without a
separate assumption for each local action. Empty states use the exhausted-state
rule. Nonempty rows without actions still require external module contracts;
residual SN, initial knowledge and finite execution remain explicit premises.
Missing witness/context rows, missing action evidence and orphan witnesses are
rejected. This does not discharge Split boundaries or certify a source root.

Native diagnostic 2710 confirms both original observed-spine sites retain their
required observations: region 0/local 23 and region 35/local 3. The unchanged
native binary also passes the renamed producer/consumer acquisition fixture
(4.50 seconds) and the finite-head context/mutation regression. Evidence is
Ferrum `target/prolog-separation-head-check-2710/{inventory,fixture,head}.log`.
The inventory includes clause-shaped stack-split rows; these are not additional
resolution actions. The actual resolution count remains eight.

The first incremental code-generation check exposed a non-executable existential
list tail in `lpp_check_fresh_univ_clause`. An equivalent proved list-pattern code
equation preserves the logical predicate, freshness conditions and soundness
proof. The failed export and corrected attempts are retained with the resident
log; this is a Prolog integration issue, not an unrelated tool issue.

Resident 2045–2052 and their corrected reloads pass with zero oracles/skips.
The combined dispatcher initially loads in 5.675 seconds; the final table proof
reload takes 0.983 seconds. Ten additional head/unification regression lemmas
pass. The complete local-table predicate generates 439,932 bytes of SML in
34.801 seconds and compiles successfully in Poly/ML. The generated module is
unchanged; the external compile wrapper supplies the standard reference alias
and disables the `before` infix notation. Generated SHA-256 is
`a7a82ae184bec72e7c886cd24b77ac20170ad51e1be6c2537ad3de4eeba41b67`.
Artifacts: `target/prolog-separation-check-code-2053/`, including the export driver,
compiler wrapper, generated module and compile logs. All attempted loads and
corrections are retained in `target/prolog-separation-dispatch-2045-2053-resident.log`.
The standard in-process compiler check lacked `ISABELLE_TMP`; the explicit
persistent-directory workaround is recorded in Ferrum's non-Prolog issue log.

This was an incremental local code-generation/compilation check, not a rebuilt
unified checker, source certificate or new benchmark gain. Remaining work is to
serialize the native reconstructed tables and local evidence, bind source/query
initialization, compose explicit Split/module return contracts, discharge the
structural residuals, and run original-source audits and strict unified-checker
replay. The goal stays active. Next native 2711, resident 2054.

## Native local-evidence serialization and parser (2711; 2054–2055)

Ferrum now reconstructs the local dispatcher choice for every original local
state. Conditional head receipts must have their actual observed-spine premise
before selection. Fresh/reflexive/pair/univ choices reference only the bound
parent's reconstructed traces; missing or changed rows fail fresh validation.
Serialization validates the complete parent and uses the existing source data
encoding, retaining source predicate symbols separately from data symbols.

`LP_Prolog_Separation_Witness_XML` parses this evidence using the common symbol,
term and binding parsers. It exposes no accepting source-proof constructor.
Resident parser definition/reload takes 0.480/0.533 seconds; incremental SML
parser export takes 13.752 seconds. The unedited generated parser compiles and
reads all five original files: regions 0/19/28/35/47 have 30/4/3/10/21 rows.
Every dispatcher-family count matches the native inventory. Missing fresh binding
fields and unknown witness tags are rejected. Evidence:
`target/prolog-separation-witness-2054-2055-resident.log` and
`target/prolog-separation-witness-parser-2055/{Check.ML,check.log}`; native files
are in Ferrum `target/prolog-local-witnesses-2711/xml/`.

The 68 rows comprise 30 absent rows (23 exhausted, 7 module boundaries),
21 ordinary actions, 3 ground equalities, 6 finite-head resolutions, and 2 each
of pair, reflexive, fresh and univ evidence. Absence is not a module proof.
The renamed acquisition fixture, missing-row serialization mutation, finite-head
and univ regressions pass. No full rebuild, unified checker export or certified
gain. Next serialize actual table states, contexts, functor/separation facts,
actions and exact links; bind source/query and explicit Split/module contracts,
then discharge residuals and strictly replay. Next native 2712, resident 2056.

## Complete native state transport (2712; resident 2056)

`LP_Prolog_Separation_State_XML` decodes complete node, annotated return-state,
source-context, free-variable, functor and separation arrays. It reuses the shared
node/return/context parsers and has no accepting proof constructor. The native
serializer freshly validates the owning graph receipts and retains observations
from saved frames as well as the active frame. Source-data encoding preserves
the predicate/data distinction.

Incremental resident loading passes (1.755 seconds), as does parser generation
(15.327 seconds, 88,746 bytes). Unmodified generated SML parses all five original
regions with matching six-array lengths: 30/4/3/10/21 rows, totalling 68. The
14 functor observations and eight separation facts survive decoding. Missing
context fields and incomplete functor facts reject. Evidence is in
`target/prolog-separation-state-parser-2056/{Separation_State_Export.thy,Check.ML,check.log}`;
native XML and inventory are in Ferrum
`target/prolog-state-serialization-2712/`. The harness initially had an extra
parenthesis; correcting that harness syntax produced the recorded successful run.
Generated checking code was not edited.

This checks serialization only. Actual action/link checks, source/query
initialization, explicit module return contracts, residual discharge and unified
strict replay remain necessary. No unified export or new certified gain.
Next native 2713, resident 2057.

## Original local action checks (2713; resident 2057–2059)

Added shared-parser integration for complete per-node links, functor actions and
local source/residual subjects. Native ordinary action serialization reuses the
LP-with-cut return serializer, supplied with freshly reconstructed projected links.
All witnesses, states, links, actions and subjects parse in one generated module.
This remains diagnostic assembly: no query/profile binding, module boundary
proof or residual termination is implied by parsing or a local side check.

Actual generated checks found a producer encoding mismatch in anchored/spine-head
symbols. After correction all 38 local separation side checks pass; 32 source
checks pass. Six remaining source failures: region 0 nodes 6,10,22,23 and region
47 nodes 6,10. For both univ rows, diagnostic removal of only the target argument
spine observation changes rejection to success; the actual graph/evidence retains
that fact. The general functor-context checker needs checked spine acquisition.
Other failures survive removal of target observations and require further
resolution/refresh link diagnosis. No rule was weakened to accept these rows.

Parser generation 2057/2058 takes 14.943/15.526 seconds. Combined local checker
2059 takes 45.226 seconds, 524,984 bytes; unmodified generated SML executes against
all original regions. `target/prolog-separation-local-check-2059/Check-Fixed.ML`
asserts exactly 38 local successes and 32 source successes; check-fixed.log and
Diagnose.ML/diagnose.log retain details. Initial harness type/indexing errors are
saved separately. Native evidence is Ferrum `target/prolog-link-serialization-2713/`.
The renamed fixture and four shared return serializer tests pass. No unified
checker rebuild/export and no certified root gain. Next native 2714, resident 2060.

## Checked functor-to-spine context acquisition (2060–2065)

`LP_Prolog_Functor_Shape_Context` now derives the existing argument-spine shape
from an actual functor observation. The shared evaluation functor link augments
its source context with precisely these proved shape facts before using the
existing context transport checker. The observation requires neither integer
inputs nor finite elements. Existing source observations remain required. The
spine grammar and argument-shape lemma moved to this lower dependency layer to
avoid importing the later module/return development into local link checking.

Both evaluation and stable context augmentation are proved; their shared link,
separation and univ witnesses use the same enriched source valuation. Empty
functor extensions keep the old checker equation. The full affected dependency
chain through `LP_Prolog_Separation_Subject_XML` passes (resident 2064), including
all existing missing-fact/changed-argument and spine distinctions. New acquisition
lemmas have no oracles or skipped proofs. Initial proof-method and stable-context
refinement errors were fixed and retained in
`target/prolog-functor-shape-2060-2065-resident.log`.

Incremental export 2065 takes 44.562 seconds, 525,565 bytes. Unmodified generated
SML checks the exact native 2713 xml-fixed inputs: all 38 local checks still pass,
and source-action successes improve from 32 to 34. Both original univ rows now
pass with their argument-spine observations intact. Fresh-variable collision and
unjustified target-shape mutations reject in both regions. Evidence:
`target/prolog-functor-shape-check-2065/{Functor_Shape_Export.thy,Check.ML,check.log}`.
No native rebuild was needed; no unified export or root gain is claimed.

Four source failures remain: region 0 nodes 10,22,23 and region 47 node 10.
Further generated-checker diagnostics in 2059 establish that the reflexive rows
pass base equality, bounds, return values, ordinary return links, context transport
and functor transport; their free-variable link check fails. The two resolution
rows pass when only the target functor facts are removed in diagnostic copies,
so their exact functor transport requires strengthening. The real tables retain
all facts. Next: checked equation-aware functor transport and context-justified
reflexive free-variable preservation, then module contracts/residual discharge.
Next resident 2066; native remains 2714.

## Equation-aware functor transport (2066–2073)

`LP_Prolog_Functor_Equation_Transport` compares all three terms of a source
relation with an instantiated target relation under the actual checked link
equations. It uses the existing `lp_normalize_goals` and its soundness theorem;
normalization failure cannot discharge the comparison. Exact relation matches
remain accepted. With no equations, the new transport is proved equivalent to
the old exact transport. No source relations, contexts or failure branches are
removed. The changed-argument negative lemma now explicitly has empty equations:
a checked equation may legitimately identify two argument variables.

Evaluation, stable, separation and univ link witnesses are updated. The full
affected dependency chain through `LP_Prolog_Separation_Subject_XML` passes at
2072. New soundness proofs have no oracles or skipped proofs. Proof attempts,
including an interrupted over-broad Metis attempt and corrected syntax/fuel
instantiation errors, are retained in
`target/prolog-functor-equations-2066-2073-resident.log`.

Incremental local checker generation 2073 takes 44.162 seconds (526,404 bytes).
Unmodified generated SML on the same 2713 xml-fixed evidence now passes all 38
local checks and 36 source-action checks: both resolution rows (0:22,0:23) close
with their functor facts intact. Argument renaming justified by an equation
accepts; missing equations, missing source facts and unjustified changed names
reject. Existing univ collision/shape mutations still reject. Check.ML/check.log
in `target/prolog-functor-equation-check-2073/` assert these results; the initial
SML harness value-restriction failure is retained separately.

The only remaining local failures are reflexive rows 0:10 and 47:10, specifically
free-variable preservation. The next general route can use the existing shared
`lpc_mgu_unify_context_factor` with identity as comparison when a checked context
equation establishes equal operands. This yields preservation for free variables
occurring in continuation templates, without requiring finite runtime terms.
Then refresh those variables into the actual resolution environment and expose
the result as another proved free-set choice. Keep the old conservative choice
and every other link requirement. Module/return contracts, residual proofs,
source/query binding and strict unified replay still follow. No root gain,
native rebuild or unified export. Next resident 2074; native remains 2714.

## All original local tables checked (2074–2078)

`LP_Prolog_Reflexive_Free` proves preservation of free variables occurring in
continuation templates when the actual operand values are equal. It instantiates
the shared `lpc_mgu_unify_context_factor` with identity comparison, then proves
variablehood and injectivity after substitution and the existing resolution
refresh. Runtime terms need not be finite. The executable choice uses a checked
source-context equation and explicit occurrence/namespace bounds; otherwise it
uses the previous untouched-free choice. Successful and failed branches retain
their separate environments.

The functor equality checker and its evaluation, stable and separation proofs
use this result. The complete affected dependency chain passes at 2077. The new
proof group has no oracles or skipped proofs; initial spacing syntax errors are
retained in `target/prolog-reflexive-free-2074-2078-resident.log`.

Incremental export 2078 takes 44.518 seconds (531,908 bytes). Unmodified generated
SML now passes all 38 local side checks and all 38 source-action checks on unchanged
native 2713 xml-fixed evidence. The complete `lpp_check_separation_control` also
accepts all five local tables (68 rows total). Removing an action, context or
witness row rejects in every table. Removing the reflexive source equation rejects
both its side check and source action at rows 0:10 and 47:10. Prior univ and
relation-transport controls still pass. Evidence:
`target/prolog-reflexive-free-check-2078/{Reflexive_Free_Export.thy,Check.ML,check.log}`.
No native rebuild, full rebuild or unified export.

This completes actual local table checking, not a source certificate. The 30
absent rows still comprise 23 exhausted states and seven explicit module-boundary
obligations; acceptance of a local table does not discharge nonempty absent rows.
Next bind these five established regions and nested Splits into a referenced
module proof graph, check every boundary interface and actual-success return
contract, then solve its exact residuals and bind source/profile/query before
strict unified replay. Reuse the existing shared actual-return Split theorem;
do not switch to the independent source-composed graph builder or reset contexts.
Priority 1 remains unfinished. Next resident 2079; native 2714.


### Module context and actual-return interfaces (2079–2082)

The unchanged local checker export 2078 accepts context and functor transport
for all five numbervars boundaries entering local modules: 0:19 to 19, 0:25
to 28, 35:5 to 28, 47:17 to 35 and 47:19 to 19. These checks use native 2713
xml-fixed equation-refined contexts and the identity execution substitutions
reconstructed in native 2715. Empty source context rejects every nonempty target
context; adding an unsupported ground observation rejects all five connections.
The two Split targets still require their own context/interface instantiations.

`LP_Answer_Post_Actual` adds a shared answer-contract postcomposition rule and
an uncovered-actual-return rejection lemma. `LP_Prolog_Module_Return_Interface`
uses the existing commuting interface lift and start relation to compose a
module boundary with different caller/callee answer tuples. The return bridge
is required only for actual successful execution, but remains an explicit
premise independent of child termination. No operational semantics is added.

All four new theorems pass the inherited-oracle and skip-proof audit. Resident
2082 checks the small new theories in 0.175 and 1.848 seconds; no rebuild or
code export. The first diagnostic attempts had SML value-restriction type
errors; the initial generic rejection proof used an unconstrained blast search
and was interrupted after 31.855 seconds, then replaced by an explicit proof.
All attempts remain in `target/prolog-module-context-2079/`, including
`Check.ML`, `check-controls.log`, `return-interface-resident.log` and the
resident-written trust-checked `proofs-2082.log`.

These are proof lemmas and boundary checks, not an accepting root constructor.
Concrete interface maps, actual-return bridges, the two Split contracts, global
residual discharge, source initialization and unified strict replay are still
required. Numbervars remains UNKNOWN; priority 1 is unfinished. Next resident
2083, native 2716.


### Shared caller/callee return interfaces (2083–2086)

Concrete boundary inspection shows that neither side's answer tuple necessarily
determines the other. The new shared interface concatenates caller outputs and
instantiated callee outputs per saved frame. Independent coordinate projections
recover each original tuple. This retains shared and caller-only terms under
runtime substitution; it does not assume that missing coordinates stay constant.

`lpp_domain_shared_interface_boundary` composes the two commuting projections
with the separately required actual-success bridge. Its checked specialization
uses the existing `lpc_check_return_projection` on both sides. There is no new
execution semantics or finite-term assumption. Both new theorems pass the
inherited-oracle and skip-proof checks. Two initial attempts to instantiate the
checked theorem produced ambiguous higher-order unification; explicit projection
functions and sequential proof premises resolve it.

Incremental export 2086 takes 20.504 seconds and produces 90,215 bytes. The
unmodified generated checker accepts all five numbervars local-module boundary
interfaces decoded from native 2713 xml-fixed, and rejects erased shared tuples
and invalid caller/callee projection indices at every connection. The test
harness supplies ordinary structural SML equality for the generic checker;
its first attempt incorrectly supplied string equality and is retained.
Evidence: `target/prolog-shared-return-interface-2084/`, especially `Check.ML`,
`check-fixed.log` and resident-written `proofs-2086.log`. Native 2716 constructs
all seven shared interfaces and checks full reconstruction and bound callee
return variables. The two Split interfaces retain their separate contracts.

A shared interface is not the actual-success residual bridge. Concrete return
relations, nested Split contracts, the referenced module assembly, global
residual discharge and source/unified replay remain unfinished. No new root
verdict or unified export. Next resident 2087; native 2717.


### Observation coordinates through actual returns (2087–2090)

Concatenating caller/callee output tuples alone omits observation-only fields:
numbervars boundary 47:17 needs the functor-name variable V3, and 0:25 needs V1.
Native 2717 appends the complete source/answer/free/context/observation variable
interface, preserving both prior projections. Its explicit variable-to-coordinate
route is reconstruction evidence, not an assumption of stable variable values.

`LP_Prolog_Return_Functor_Route` checks coordinate bounds, exact variable entries
and coverage of every functor observation term using the shared
`lpc_check_return_route`. Its initialization lemma and actual-return theorem
preserve the complete functor relation under runtime substitution. Every saved
frame must satisfy routing; no finite-term or integer premise is introduced.
The two theorems pass the inherited-oracle and skip-proof audit. Early incomplete
case proofs were replaced by explicit observation-constructor reasoning.

Export 2090 takes 25.018 seconds (117,132 bytes). Unmodified generated code checks
all five actual local-module shared interfaces with the ambient coordinates
reported by native 2717. The two nonempty observation sets (0:25 and 47:17) pass;
missing routes and erased tuples reject. Evidence is in
`target/prolog-return-functor-route-2090/{Check.ML,check-fixed.log,proofs.log}`;
the first harness attempt's wrongly cased typeclass field is retained in check.log.
This is a local export, not a unified rebuild or root verdict.

The successful-return relation is now preserved in the shared coordinates, but
its concrete residual bridge, nested Split contracts, full referenced assembly,
residual termination and original-source/unified replay remain required.
Priority 1 is active. Next resident 2091; native 2718.


### Matching-head structural preservation (2091–2098)

The 2718 native audit found an 11-step cycle in the unconstrained local-control
residual. The first loss disconnects a finite call from its refreshed matching
head. `LP_Prolog_Matching_Structure` now derives a stronger observation from the
shared MGU variant theorem: every finite runtime call has a finite template,
and matching-head resolution preserves that template up to one injective
variable renaming. Both constructor structure and sharing survive. Runtime
variable identities need not remain equal, so this does not justify inserting
old/refreshed runtime equations into existing links.

The checked specialization consumes the existing `lp_cut_check_match` receipt,
actual MGU and finite-call premises. A companion constructor-argument theorem
retains the actual child templates in a finite univ observation. Negative
lemmas exclude constructing a node by variable renaming, merging distinct
variables under an injective renaming, and representing a cyclic runtime term
by a finite template. No new operational semantics or graph constructor.

All seven theorems pass with zero oracles and no skipped proofs; resident 2098
loads the theory in 1.725 seconds. No export, native rebuild or unified build.
Evidence is `target/prolog-matching-structure-2091-2098/{proofs.log,resident.log}`.
Attempts retain the reserved-name/type-inference errors and explicit list
instantiation corrections; one unconstrained negative-control blast proof was
interrupted after 19.077 seconds and replaced by a direct finite-term argument.

This proves the semantic preservation needed by a stronger residual encoding;
the current native residual and its spurious cycle are unchanged. Next expose
and transport these structural templates in the residual relation, including
univ and observed-spine head cases, before finishing return/Split assembly and
strict source replay. Numbervars remains UNKNOWN. Next resident 2099, native
2719; priority 1 is active.


### Finite structural observations (Isabelle 2099–2100)

`LP_Prolog_Structural_Observation` gives finite runtime templates a ground
structural encoding: constructor labels and children remain; runtime variable
names become a distinguished leaf. This additional observation does not replace
runtime sharing, rational equations or source contexts. Matching-head MGU
resolution preserves the observation under variable renaming. A finite
constructor-argument observation exposes the same actual child templates for
univ, and each child has its corresponding structural observation. Cyclic
runtime terms cannot initialize this finite observation.

All eight lemmas pass Isabelle with zero inherited oracles and no skipped
proofs. Final incremental load took 0.748 seconds; no native or unified rebuild.
Resident-written evidence is in CeTA
`target/prolog-structural-observation-2099-2100/proofs.log`. The initial edit's
malformed equation separator was corrected before verification.

This does not yet strengthen the native residual: the recorded 11-step cycle
remains a required negative regression. Native transport must consume these
observations, including observed-spine resolution and helper substitutions;
matching-head preservation is not arbitrary-substitution preservation. Complete
return/Split assembly, residual discharge and original-source strict replay
remain outstanding. The certified total stays 90 YES + 97 NO; numbervars is
UNKNOWN. Priority 1 remains active. Next resident 2101, native 2719.


### Structural equations and executable univ relation (Isabelle 2101–2108)

`LP_Prolog_Structural_Projection` proves unique finite structural observations
and compositional evaluation of source terms in a separate structural
environment. The existing checked matching receipt now yields an equation
between projected pre/post terms, without equating their runtime environments.
The observed-list-head variant derives the same equation from a proper spine,
actual successful MGU, distinct head fields and complete argument coverage.
Arbitrary successful instantiation is explicitly not structure preservation.

`LP_Prolog_Structural_Univ` connects the actual constructor-argument observation
to an executable finite relation retaining constructor identity, ordered child
structure and the corresponding list. Its premise requires initialized finite
observations; a rational cyclic graph cannot supply them. All nine new lemmas
pass with zero inherited oracles and no skipped proofs. Projection load 2104
took 1.573 seconds; univ load 2107 took 1.244 seconds. Earlier attempts exposed
reserved identifiers tau/args and an induction fact naming error; corrected.

Local export 2108 took 1.492 seconds and produced 19,864 bytes. Unmodified
generated SML passes 24 controls over three constructor names, including changed
labels, dropped/reordered children, variable sources, renamed variables,
structure-changing instantiation and nullary constructors. Evidence is CeTA
`target/prolog-structural-projection-2101-2108/{proofs.log,Check.ML,check.log}`.
No native or unified rebuild; no new benchmark verdict.

The remaining integration must encode these relations in the actual residual,
retain runtime facts independently, and transport observations through module
interfaces and actual helper returns. The present structural univ relation is
an executable check on finite values, not yet a finite common-LP/TRS encoding
of arbitrary constructor labels and arities. Do not silently enumerate only
source-mentioned constructors or claim that symbolic runtime variables are
constant structural leaves. The 2718 cycle remains unchanged until that
integration is checked. Return/Split assembly, residual discharge and strict
source replay remain required. Total: 90 YES + 97 NO; priority 1 active.
Next resident 2109; native 2719.


### Finite constructor encoding and native structural receipts (2719 / 2109–2117)

`LP_Prolog_Reified_Structure` represents constructor labels as data under fixed
node/list constructors. Two generic rewrite rules convert the encoded child
sequence into the encoding of the actual Prolog argument list. The theorem
`lpp_actual_univ_reified_conversion` connects this ordinary `Trs.rstep` path to
the actual constructor-argument relation and initialized finite observations;
it does not enumerate source-mentioned labels or bound input arities. Reification
commutes with structural substitution and preserves the previously checked
structural equations. This is a residual encoding, not a new source semantics.

Eight theorems pass with zero inherited oracles and no skipped proofs. Final
resident load 2117 took 6.093 seconds; resident-written evidence is CeTA
`target/prolog-reified-2109-2115/proofs-2117.log`. Attempts retain corrections
for the imported parser's rstep name, tuple-shaped function cases, reserved
output identifier, and an explicit map-congruence proof. No unified export.

Native `source_reified` implements separate expression/template encoders:
symbolic variables retain structural-environment obligations; only concrete
finite templates erase variable names to leaves. Recognized integer/binary64
atoms remain constructor data, without asserting integer arithmetic coverage.
Rational graphs and unresolved dynamic applications reject. The same two
conversion rules work for arbitrary labels and arities. Tests use the existing
shared outermost rewrite enumerator; only a test-only re-export was added.

ResolutionContext now retains a separately typed conditional structural equation
for matching and observed-spine heads. It reconstructs from the original
incoming context, source clause and resolution namespaces, with the caller's
fuel. It is never inserted as a runtime SourceContext equation. Ground-anchored
resolution does not automatically get this stronger contract. The equation
still requires finite observations, actual source resolution and the appropriate
matching/spine side conditions before a source checker can use it.

Native 2719 passes three focused tests, including twelve label/arity cases,
removed converter rules, rational rejection, leaf/instantiation distinctions,
numeric atoms, and erased/changed structural receipt controls. The generalized
Split/spine fixture passes in 12.80 seconds; saved-context/failure transport also
passes. Incremental final build took 24.35 seconds. First builds exposed a
private test-helper import and a test lowering path typo; both are fixed.
Evidence: `target/prolog-reified-2719/`.

The actual numbervars diagnostic passes in 2.41 seconds and reconstructs six
conditional structural equations: matching at 0:2, 0:3, 47:2, 47:3 and observed
spines at 0:23, 35:3. This includes the first known structural disconnect.
The unmodified control residual still validates its 11-step loop; no strengthened
residual or source verdict is claimed. Next consume the structural coordinates
and converter paths in complete residual generation, bind them in the source
checker, and handle actual helper returns/Splits before residual discharge and
strict replay. No strategy, guidance format or accepting state representation
changed here. Total remains 90 YES + 97 NO; priority 1 active.
Next native 2720; resident 2118.


## Reified structural control contracts — 2026-11-18

`LP_Prolog_Reified_Argument_Program` proves successful execution of the two
relational converter clauses in the existing LP answer semantics.
`LP_Prolog_Reflexive_Structure` proves finite observation preservation from
an inverse substitution, then specializes it to initialized reflexive unification
on variables covered by the active continuation.
`LP_Prolog_Separated_Pair_Structure` proves the analogous result for binding
two distinct fresh variables to a finite pair, requiring actual runtime support
separation. Syntactic variable disjointness alone is insufficient.

Resident checks 2118/2120/2121 pass without oracles or skipped proofs; logs are
`target/prolog-reified-lp-2118-2120/`. Attempt 2119 needed an explicit string
variable-environment annotation. No unified export/rebuild was performed.
Ferrum attempt 2720 uses these conditional relationships in a diagnostic
76-clause control fragment and obtains a triples/PiDP child through the shared
scheduler. The existing unified composed-1792 executable checks that child
twice and rejects missing proof components. This does not check a complete
Prolog source assembly: observation initialization, source connection and
Split/actual-return coverage remain required. No benchmark verdict is added.


### Structural initialization and actual converter success

`LP_Prolog_Structural_Initialization` adds five checked lemmas: observation
groundness, a shared finite-observation environment, initialization through the
existing query environment, the free-variable case, and successful relational
conversion for actual source constructor arguments. Finiteness remains an
explicit premise; runtime groundness is not required. Attempt 2123 passes with
zero oracles/no skipped proofs (0.384 seconds for the new theory); receipt:
`target/prolog-reified-lp-2118-2120/initialization-2123.log`.
Attempt 2122's broad metis proof was replaced by explicit membership reasoning
after interruption. The resident was restored from the existing verified 1748
heap. No export or checker rebuild. Ferrum's weaker diagnostic child query
requires only ground structural coordinates and still passes two checks with
the pinned composed-1792 unified checker. Full source/Split assembly is pending.


### Checked Split composition with finite actual continuations

`LP_Prolog_Checked_Split_Composition` combines the existing executable Split
shape check with the shared Prolog domain-answer semantics, finite continuation
composition and actual-return projection. It retains explicit child-contract,
finite-state preservation and actual-return bridge premises. Resident 2125
passes without oracles/skipped proofs (2.284 seconds); 2124's local-definition
error was corrected with explicit interface equalities.

Native serialized Split shapes for both numbervars sites and a renamed unary
counter-marker fixture pass 24 kernel-replayed checks, including missing routing,
invalid projection, changed prefix, missing continuation and missing interface.
Generated theories/manifests and `verified-2125-2129.log` are in
`target/prolog-checked-split-2125/`. Checks 2128/2129 take 9.124/8.982 seconds;
2126/2127 needed concrete symbol types for otherwise polymorphic answer lists.
The checked data is a local composition premise, not a whole source certificate.
No unified export/build; actual-return discharge and complete assembly remain.


### Finite execution with suspended continuations

`LP_Prolog_Attached_Finite_Actions` proves the exact per-frame finiteness condition
for `lpc_attach_answers` and transfers existing finite action rules to that full
state. Matching resolution, ground/reflexive equality, separated pairs and
active simple steps are covered with their existing semantic side conditions.
Negative controls retain nonfinite suspended values and saved environments as
obligations. Eleven theorems pass with no oracles/skipped proofs in resident 2134
(2.672 seconds); evidence: `target/prolog-attached-finite-2134/proofs.log`.
Attempts 2130–2133 corrected an imported-name collision and explicit case
reasoning. The restored resident loaded the required existing control theories;
no unified export/build occurred. Native Split receipts now retain the exact
returned continuation-finiteness obligations. Complete source invariant coverage
and return/residual assembly remain outstanding; no new source verdict.


### Actual-call composition with separate return properties

`LP_Prolog_Actual_Call_Composition` proves that a constant residual return contract
carries exactly termination, then instantiates finite continuation composition
with independently justified actual-answer properties. It supplies no returned
value facts from termination alone. Both theorems pass in resident 2135 with
zero oracles/skipped proofs (0.387 seconds); evidence:
`target/prolog-actual-calls-2135/proofs.log`. No unified export/build.
Ferrum's all-calls diagnostic includes both Split continuations (78 clauses);
the common triples processor now reports `no separating triple filter`.
Input/output structural return relations and complete source certification
remain open; no benchmark verdict is added.

### Bounded leaf instantiation and structural descent

`LP_Prolog_Bounded_Instantiation` connects finite runtime substitution images to
an inductive structural return relation. Existing constructors are retained;
variable leaves may stay free or become an explicitly allowed finite template.
Composition tracks the runtime support of the first substitution and requires
ground replacement templates. This is a conditional source-return theorem, not
an assumption inferred from helper termination.

A weighted structural measure reserves a bound at each free leaf. Checked
replacement does not increase this measure, and descent to a constructor child
remains strict after replacement. Binary constructors with two atomic children
have weight three regardless of their labels. Controls reject cyclic images,
unapproved constructor introduction, changed constructor identity and an
insufficient leaf budget. Template sets need not be finite; a uniform budget is
an explicit independent premise.

All 13 theorems pass in resident 2148 (1.208 seconds), with zero oracles and no
skipped proofs. The resident-written receipt and theory hash are in
`target/prolog-bounded-instantiation-2148/`. Attempts 2141–2147 corrected explicit
disjunction/membership reasoning, a lexical signed-comparison ambiguity and
higher-order premise instantiation; 2141 was interrupted without restarting the
resident. No unified export or rebuild. Actual source return-bound synthesis,
relational residual emission and full source assembly remain open. No benchmark
verdict or checker acceptance changed.

### Source equality and parameter-dependent leaf budgets

`LP_Prolog_Bounded_Unify` derives bounded images from an actual most-general
source equality binding a variable to an allowed finite ground template. Other
observed variables must occur in the continuation. A kernel counterexample shows
that an MGU can freely change an unobserved variable; coverage cannot be omitted.
The resulting actual substitution produces the checked structural leaf effect.
Three theorems pass in resident 2150 (1.479 seconds).

`LP_Prolog_Parameter_Leaf_Budget` gives a uniform budget for a binary marker whose
second child is either an initial finite ground parameter or any atomic result.
The budget depends on the initial parameter's structural size. This matters:
successful arithmetic does not imply that its input expression was atomic.
Three theorems pass in resident 2154 (0.440 seconds). Attempt 2151 needed a
specialized equality, 2152's broad simplification was interrupted, and 2153
corrected a theorem name. The resident stayed running.

All six theorems have zero oracles/no skipped proofs. Resident-written receipt
and theory hashes: `target/prolog-bounded-unify-2150-2154/`. No unified export or
full build. Actual recursive helper-return coverage, all source actions and the
relational residual implementation remain necessary; there is no new verdict.

### Bounded scalar results, including binary64

`LP_Prolog_Bounded_Arithmetic` proves bounded substitution images and structural
leaf effects for successful evaluation through the existing stable scalar
semantics. It requires allowed atomic results, not integer-only inputs or atomic
input expressions. Three theorems pass in resident 2158 (0.314 seconds).
Attempts 2155–2157 needed an explicit atomic witness and a concrete template
variable alphabet; no semantic premises were weakened.

The parameter template family now also admits atomic leaf replacements, since
an arithmetic result can share a caller-observed variable. Groundness and its
uniform parameter-dependent bound were rechecked in 2155 (0.452 seconds).
All five checked theorems have zero oracles/no skipped proofs; resident receipt
and theory hashes: `target/prolog-bounded-arithmetic-2158/`. No checker build.
Ferrum's diagnostic relational compiler closes through the common scheduler;
the standalone child passes twice with the pinned composed-1792 unified CeTA.
Its missing-component mutation rejects. This does not establish recursive
source return coverage or a complete benchmark certificate.

### Successful execution of the bounded leaf relation

`LP_Prolog_Leaf_Relation_Program` proves the emitted relation's execution in the
existing `lp_seg_answer_step` semantics. Core clauses preserve the parameter
vector, constructor labels, caller environment and arbitrary residual tail.
Given explicit replacement-clause coverage, induction through constructor/list
children realizes every allowed leaf effect as a successful residual path.
Ten theorems pass in resident 2170 (2.432 seconds).

`LP_Prolog_Parameter_Leaf_Program` discharges replacement coverage for copied
initial parameters, atomic markers and plain atomic results, then specializes
the successful-execution theorem. Both theorems pass in 2171 (1.656 seconds).
All twelve have zero oracles/no skipped proofs; receipt and hashes:
`target/prolog-leaf-program-2170-2171/`. Attempts 2159–2169 corrected explicit
map reasoning, imported-name/lexical collisions, clause-instance selection and
list induction binder order. Only the new theories were loaded; no checker build.

The native seven-clause family closes through common triples solving and passes
two pinned unified checks; missing component rejection is retained. This proves
residual realization conditional on source effects. It does not discharge actual
recursive helper returns, matching/univ preservation, source assembly or replay.

### Composing leaf effects and preserving active matching contexts

`LP_Prolog_Leaf_Effect_Composition` proves transitivity when replacement templates
are ground. A concrete nonground counterexample shows that two permitted steps
can otherwise introduce a nested constructor not allowed by the original effect.
Six theorems pass in resident 2175 (0.771 seconds); 2172's unavailable list cases
rule was replaced by explicit list cases in 2173.

`LP_Prolog_Matching_Context_Structure` derives an inverse substitution from the
existing MGU contract for variables in both the selected atom and the active
continuation. Every finite observed caller value retains its structural
observation. Saved alternatives and uncovered answer-only variables are not
silently included. Two theorems pass in 2174 (2.769 seconds). All eight have zero
oracles/no skipped proofs; resident receipt and theory hashes:
`target/prolog-leaf-composition-matching-2174-2175/`.

Native matching structural receipts now retain active-context equations and
validate them by reconstruction. The complete numbervars all-calls diagnostic
is byte-identical to its earlier 78-clause subject and still fails triple
filtering. These results establish local transport/composition obligations;
actual recursive return invariants and full source assembly remain open.
No unified checker export or full rebuild.

### Runtime leaf invariants belong to attached execution

`LP_Prolog_Runtime_Leaf_Invariant` relates an initial structural observation to
an actual current runtime value. It proves initialization, finiteness, bounded
substitution transport and transport through matching, reflexive equality,
allowed ground binding and stable scalar arithmetic. These are conditional local
source rules, not a completed graph invariant.

`LP_Prolog_Attached_Leaf_Composition` specializes the existing shared invariant
composition theorem to termination with caller-return facts. Preservation is
required along attached execution; continuation facts are extracted from that
invariant at prefix completion. A standalone prefix can overapproximate changes
to variables absent from its active goals, so requiring a leaf bound on every
standalone return would be too strong. A checked two-step actual-return example
in the shared cut semantics demonstrates this issue. A separate control rejects
stale saved-environment facts. No source transition or MGU rule was changed.

All sixteen new theorems pass in resident 2179; the attached theory takes 1.642
seconds. Attempt 2177 corrected an imported `entry` name and specialized the
invariant explicitly. Evidence and hashes: `target/prolog-runtime-leaf-invariant-2179/`.
Zero oracles/no skipped proofs; no checker rebuild.

The parameter family additionally admits direct copies of the initial ground
value. Groundness, the unchanged uniform bound, replacement coverage and
successful residual execution pass again in 2180 (0.409/1.725 seconds for the two
theories); receipt/hashes: `target/prolog-copied-parameter-leaf-2180/`. Actual
source row coverage, attached finite/leaf invariants and complete assembly remain
open. The native eight-clause child is certified independently, not as a root.


### Checked free-variable structural initialization

`LP_Prolog_Structural_Initialization` derives a concrete structural leaf from
`lpc_free_knowledge F rho` and membership in `F`. Uniqueness identifies any
existing observation with that leaf. Runtime coordinates remain unrestricted;
query output modes alone do not establish freeness. Both lemmas pass the resident
Isabelle kernel audit without oracles or skipped proofs. Receipt and theory hash:
`target/prolog-free-initialization-2183/`. Initial loading passed in 2182
(0.408 seconds); receipt retrieval corrected the qualified `Draft` theory name.
No checker export/build or source verdict was added. Actual-state initialization
and transport remain premises of the eventual source assembly.


Ground runtime values also preserve their structural observations under
substitution. `lpp_ground_structural_observation_substitute` passes resident
2186 in 0.360 seconds, with zero oracles/skipped proofs; evidence/hash in
`target/prolog-ground-observation-2186/`. The substitution uses one runtime
variable type. Attempts 2184/2185 corrected the type and reserved identifier.
Native diagnostic projection retains these conditional observations only on
successful resolution branches. This removes its immediate separating-filter
failure, but the DP child search times out: no source verdict is established.


### Ground-observation successful-prefix relation

`LP_Prolog_Ground_Observation_Program` gives a three-clause recognizer for
constructor observations without variable leaves. Seven theorems establish its
shared-LP steps, successful traversal of every leaf-free observation/ground
template with unchanged caller environment, and rejection of a variable leaf
when its predicates are distinct. Resident 2192 passes in 1.674 seconds with
zero oracles/skipped proofs; receipt/hash in
`target/prolog-ground-observation-program-2192/`. Attempts 2187--2191 corrected
step instantiation, induction names and product-state elimination. No new
operational semantics or checker export.

The native diagnostic now retains this prefix before parameterized return
relations. Without it the filtered child admits an explicitly replayed cycle
using a leaf as counter: ground reified data does not imply ground source data.
With it seven of eight native DP children close and pass two checks each using
the unchanged pinned unified checker. The main Split-continuation child remains
open, as do actual-source invariant coverage and parent reconstruction. These
results do not add a Prolog verdict.


The actual-runtime bridge is also checked: finite runtime groundness plus an
existing structural observation entails the leaf-free property and successful
recognizer execution. These two lemmas pass in resident 2194 (1.686 seconds),
with zero oracles/skipped proofs; receipt/hash in
`target/prolog-ground-runtime-observation-2194/`. Attempt 2193 needed explicit
elimination of the impossible ground-variable case. This supplies the local
source premise for the recognizer; complete state transport and root assembly
are still outstanding.


### Leaf-count and argument-forest return order

`LP_Prolog_Leaf_Lexicographic_Return` proves that ground leaf replacements
never increase variable-leaf count; equality of the counts forces the entire
observation to remain identical. This yields a well-founded lexicographic
order with structural size as its second component, without a uniform bound on
replacement size. A nonground replacement counterexample keeps the leaf count
but changes structure, so groundness remains an explicit premise.

`LP_Prolog_List_Leaf_Effect` characterizes leaf effects on proper observed list
spines exactly as componentwise element effects, preserving spine length.
`LP_Prolog_Forest_Return_Order` connects a constructor observation with its
argument forest, an argument forest with its head, and a caller forest with
its returned tail. Tree and forest phases use different size offsets; list
encoding nodes are not counted as source traversal work. The runtime bridge
extracts the ordered returned tail from the existing runtime leaf invariant.
It does not infer that invariant from helper termination.

Seventeen theorems pass resident audits without oracles/skipped proofs. Verified
phases: 2197 (1.075 seconds), 2202 (1.361 seconds), 2205 (1.974 seconds). Receipt
and hashes: `target/prolog-forest-return-order-2205/`. Attempt 2198 was interrupted
after a schematic existential rule caused unification-bound warnings; explicit
list witnesses fixed it. Other attempts corrected sum membership, list-length
witnesses and the `*s` token ambiguity. The resident was reused throughout.

The native proper-list diagnostic has nine of ten checked DP children, with
two unified checks per successful child. The ordinary main component remains
open; three existing constructor-triples alternatives also time out. Next bind
the tree/forest views and return-order premises to the original module/Split
interfaces and discharge attached source invariants. No source certificate,
checker export, root gain or production promotion is claimed.


## Proper-list leaf program correspondence — 2212

`LP_Prolog_List_Leaf_Program` formalizes the two-clause proper-list wrapper
already emitted by the native structural diagnostic. Six lemmas prove empty
and cons steps, successful list execution from element executions, successful
execution from the leaf-effect relation, rejection of a variable-leaf spine,
and the combined runtime return/rank/program bridge. Parameter vectors,
remaining goals and caller environments are preserved. The combined theorem
requires the actual runtime leaf effect, ground replacement templates and a
finite observed head; it does not derive them from termination children.

Resident check 2212 took 2.508 seconds; all six theorem dependencies have no
oracles or skipped proofs. Receipt and hashes:
`target/prolog-list-leaf-program-2212/`. No checker export or full rebuild.
This closes the previously recorded wrapper execution correspondence, while
source-operation invariant coverage and complete module assembly remain open.
No source verdict is added. Next resident identifier: 2213.


## Fresh pair bindings and protected continuation values — 2218

`LP_Prolog_Separated_Context_Structure` proves preservation of finite structural
observations and the runtime leaf invariant through a separated fresh pair
binding. The general comparison-unifier lemma covers live continuation terms;
a second form covers individual source variables occurring within those terms.
The pair specialization requires distinct outputs, runtime separation from
the bound values and the protected value, finite bound values, and actual
continuation coverage. It does not cover arbitrary answer-only variables.

An actual-MGU counterexample proves that the bound output itself changes its
structural observation, even when it occurs in the continuation. This prevents
dropping the protected-value separation premise. Six theorems pass without
oracles/skips in 1.779 seconds; receipt/hashes are in
`target/prolog-separated-context-2218/`. No unified export or rebuild.

Native `FreshDecompositionConnection` currently acquires separation between the
decomposed input and fresh outputs. Source assembly must extend acquisition
and transport to the protected caller coordinate before applying this theorem.
A syntactic name comparison is insufficient. The full source invariant and
module parent certificate remain open; no new root verdict. Next resident: 2219.


## Fresh-output separation from attached callers — 2220

`LP_Prolog_Fresh_Continuation_Separation` extends the existing finite-head
freshness proof to individual live caller variables. Most-generality of the
same actual resolution covers both the caller continuation and clause body;
a body-only runtime variable cannot occur in a finite instantiated caller
value. The matching specialization simultaneously preserves the caller's
runtime leaf invariant and acquires separation, so it does not require an
unexplained post-resolution finiteness assumption.

Three lemmas pass without oracles/skips in 0.642 seconds; receipt/hashes:
`target/prolog-fresh-continuation-2220/`. Unified export unchanged.
The integration must carry these caller premises through attached composition:
a standalone helper region may omit the protected caller value. Do not insert
an invented caller into the established graph or infer MGU coverage from an
answer tuple. Next connect acquisition to the normalized reflexive/pair
sequence under that attached invariant, preserving all module obligations.
No source verdict yet; next resident identifier 2221.


## Normalized univ preserves attached caller effects — 2225

`LP_Prolog_Normalized_Pair_Leaf` proves that the actual reflexive-then-pair
unification sequence preserves a protected live caller's runtime leaf effect.
A common inverse from the first MGU transports freeness, output distinctness,
finite observations and separation together. The second MGU uses those
transported facts, not the original variable names. The final specialization
uses the constructor-name/argument-list sequence emitted for source `=..`.

The proof requires the existing initial runtime separation and continuation
coverage; acquisition is supplied by 2220. It does not assume every continuation
value is finite, only the observed protected value and the pair's bound values.
Three lemmas check without oracles/skips in 0.773 seconds; receipt/hashes:
`target/prolog-normalized-pair-leaf-2225/`. No checker generation or export.
Local composition is proved; operation-dispatch coverage and attached invariant
assembly over the complete source module graph remain open. No new source
verdict. Next resident identifier: 2226.


## Leaf invariant over shared answer-stack operations — 2229

`LP_Prolog_Leaf_Stack_Steps` lifts local environment transport obligations over
the complete existing `lpc_answer_transition`, `lpp_answer_transition` and
domain-envelope relations. The case proofs cover clause dispatch, resolution,
unification, cut pruning, backtracking, success, failure, errors, meta calls,
builtin branches, choices and probes. Saved alternatives keep their own
environments. Unsupported-domain self-loops preserve the invariant but remain
termination obligations; no stuck-state shortcut is introduced.

Local lemmas instantiate environment transport for matching resolution, stable
arithmetic, allowed ground binding and reflexive equality. Their source and
MGU-coverage conditions remain explicit. This is the assembly layer for the
attached-call invariant, not a proof that arbitrary source rows satisfy those
conditions. Ten lemmas check without oracles/skips in 5.848 seconds; receipts
and hashes: `target/prolog-leaf-stack-2229/`. No export or rebuild.

Next instantiate these conditions for the established graph's source rows,
including acquired separation for the normalized pair sequence, and connect
complete module/rank coverage. No root verdict added. Next resident: 2230.


## Observed-spine heads preserve caller effects — 2232

The original-source row audit identifies observed-spine and ground-anchored
head records beyond ordinary matching. `LP_Prolog_Leaf_Spine_Head` extracts a
matching witness for successful linear list-head resolution from an actual
proper-spine observation, then instantiates environment leaf transport. Failed
head alternatives and acquisition of the spine observation remain obligations;
finite elements are not inferred from the spine.

Two lemmas pass without oracles/skips in 0.383 seconds. Receipt/hashes:
`target/prolog-leaf-spine-head-2232/`. No checker export. Ground-anchored
return effects and allowed parameter membership remain local gaps before
complete module assembly. Next resident: 2233.


## Finite ground head effects without replacement-size bounds — 2235

`LP_Prolog_Ground_Head_Leaf` proves that bounded substitution images on the
selected call extend to every covered caller value: outside the selected call,
a restricted comparison unifier and most-generality force variable images.
For a finite ground instantiated head, selected images are finite ground
templates, giving leaf-effect preservation with the family of all finite
ground templates. Finiteness and coverage remain explicit premises.

This uses the already proved variable-leaf-count/size order, which does not
require a uniform replacement-size bound. It can remove the four-pattern
parameter-family restriction from the source rank argument. The earlier
parameterized residual proofs remain intact; broadening their generator is
not silently performed. Runtime-template reconstruction and source-row
instantiation remain necessary before parent assembly.

Four lemmas pass without oracles/skips in 0.732 seconds; receipt/hashes:
`target/prolog-ground-head-leaf-2235/`. No export or source verdict.
Next resident identifier: 2236.


## Runtime instantiation of anchored-head leaf transport — 2240

`LP_Prolog_Runtime_Ground_Head_Leaf` reconstructs finite runtime goal lists as
finite templates while proving exact preservation of variable support. This
lifts the ground-head bounded-images theorem to actual runtime calls and
continuations, and then to the existing environment-transport interface.
The final specialization consumes `lpp_check_anchored_head`, its actual ground
knowledge, argument lengths, actual MGU, finite arguments/continuation and
protected-coordinate coverage. These remain explicit source obligations.

Terminology: the existing inductive `lp_seg_ground` predicate entails
`lpp_finite_term` by `lpp_ground_finite_term`. That formal premise is stronger
than ordinary variable-free rational-term groundness. The anchored rule uses
the existing predicate and theorem; it does not reinterpret cyclic terms as
finite observations or change source semantics.

Five lemmas pass without oracles/skips in 0.944 seconds; receipt/hashes:
`target/prolog-runtime-ground-head-2240/`. No checker export or rebuild.
Next connect the complete local invariant conditions to the established source
modules and their attached caller interfaces. No root verdict. Next resident: 2241.

## Return-slot leaf coverage and node integration — 2245/2252

`LP_Prolog_Return_Leaf_Coverage` checks evaluated return payload slots against
actual selected-call/continuation support. The anchored-head stack theorem
covers all shared base transitions, retaining saved alternatives. The new
`LP_Prolog_Return_Leaf_Node_Contract` instantiates the existing checked node
contract with finite execution plus leaf preservation; it keeps source context,
branch links, residual and return obligations explicit.

The original-source audit found three resolution rows whose whole-term payload
is related to the called argument list through an existing functor fact.
`LP_Prolog_Functor_Leaf_Support` proves exact runtime support equality and an
ordered finite closure over those facts, including missing-fact and missing-
argument rejection controls. This remains valid for rational children and does
not infer finite elements from a proper spine. The closure still needs wiring
into the coverage predicate/node constructor and native certificate export.

Fifteen lemmas passed resident Isabelle with zero oracles and no skipped proofs.
Receipts and source hashes: `target/prolog-return-leaf-node-2245/` (coverage
3.183 seconds, node contract 3.882 seconds, support closure 1.200 seconds).
Only missing imported dependencies were loaded; no native/full rebuild or
unified export. No new root verdict. Remaining work includes other source
operations, relational coverage integration, attached Split/rank composition,
source certificates and strict replay.

## Relational coverage consumed by head contracts — 2257

`LP_Prolog_Relational_Return_Leaf` consumes the finite functor-support closure
inside return-slot coverage and the anchored-head node contract.
`LP_Prolog_Relational_Matching_Leaf` and `LP_Prolog_Relational_Spine_Leaf` add
matching and observed proper-list head contracts with the same combined finite
execution/leaf-stack invariant. Actual runtime matching is derived from the
successful list-head resolution; list length never supplies finite elements.
Source/context checks, failure links and saved alternatives stay explicit.

Twelve lemmas check with no skipped proofs or oracles. Resident check times:
4.961, 4.034 and 0.722 seconds. Receipt and hashes are retained under
`target/prolog-relational-leaf-2257/`. Ferrum adds a conditional coverage receipt
bound to the entire projected state and active-frame functor facts. Original
and renamed source reconstruction both cover all 12 resolution payloads; this
is coverage evidence, not certification of every source node or the root.

No unified export or new source verdict. Next integrate the nonempty separation
contracts for fresh outputs, equality/univ operations and the complete attached
Split/rank assembly. The existing empty-target head contracts do not discharge
fresh-output acquisition or replace any module dependency.

## Fresh outputs and ground equality preserve return leaves — 2269

`LP_Prolog_Relational_Fresh_Leaf` combines the existing normalized fresh-clause
separation acquisition with finite execution and relational return-leaf
preservation. Successful separation is acquired and normalized; failure retains
its incoming facts. `LP_Prolog_Relational_Ground_Equality` reuses the existing
most-generality theorem via a ground-head logical reduction. The source
semantics and established graph are unchanged.

`LP_Prolog_Ground_Return_Leaf_Coverage` admits payload variables absent from the
active goals only with explicit incoming ground knowledge, whose runtime
support is empty. `LP_Prolog_Ground_Leaf_Node_Contract` consumes this check and
preserves both invariants through the shared equality node contract. Groundness
here is the existing inductive finite-ground predicate, not unrestricted
rational groundness or integer knowledge.

Eleven lemmas check without oracles/skips, including removal of ground knowledge.
Receipts, source hashes and failed development attempts are retained in
`target/prolog-fresh-ground-leaf-2269/`. Broad automation attempts were interrupted
at 43.023 and 38.936 seconds without restarting the resident; the explicit
factor proof checks in 0.448 seconds. No unified export or source gain.
Native coverage now handles all three retained ground-equality rows as well as
all 12 resolution rows on original/renamed sources. Reflexive/pair/univ and
remaining control invariants, attached Split/rank assembly and replay remain.

## Reflexive and protected-pair leaf node contracts — 2277

`LP_Prolog_Relational_Reflexive_Leaf` strengthens the existing reflexive
separation contract with the finite/leaf invariant, using the checked source
equation rewrite and actual return-slot coverage. `LP_Prolog_Pair_Leaf_Images`
proves that a pair binding preserves variable images outside the bound outputs
when covered by the actual right-hand side or continuation.

`LP_Prolog_Pair_Leaf_Protection` checks payload separation through existing
separation facts, incoming ground knowledge and functor-support closure.
`LP_Prolog_Pair_Leaf_Node_Contract` consumes these checks with the shared pair
and equality node rules. Missing separation and bound-output observations are
rejected. Fifteen lemmas pass without oracles/skips; receipt/hashes:
`target/prolog-reflexive-pair-leaf-2277/`.

Native original/renamed audits cover slots 0 and 1 at both retained pair rows.
Slot 2 lacks a checked separation fact and remains open for this invariant;
its full payload/interface is retained. These results are conditional node
contracts, not a completed source certificate. Remaining work includes univ
normalization, administrative/builtin invariant integration and attached
Split/rank assembly. No unified export or source verdict changed.


## Leaf invariant through normalization and ordinary controls — 2282

The established `=..` separation node now carries finite execution and the
return-leaf invariant together. Normalization inserts the actual equality
sequence without changing active or saved return environments. It does not
perform the equalities: their reflexive/pair contracts remain required.
The same distinction applies to arithmetic normalization; the checked source
profile and its error/domain branches remain unchanged.

The ordinary action dispatcher now consumes this combined invariant for
administration, clause allocation, variable tests, arithmetic normalization,
trimming and parallel alternatives. Scope renaming preserves the invariant.
Existing source-action and separation checks retain every represented branch
and target condition; no graph/context reconstruction was weakened.

Eighteen lemmas pass resident Isabelle with zero oracles/skipped proofs,
including missing-context and missing-successor controls. Receipts and hashes:
`target/prolog-leaf-control-2282/`. Attempt 2280 required explicit conjunction
instantiation in the test-node proof, fixed in 2281. Only new theories and their
missing imports were checked; no native/full rebuild or unified export.

No source verdict is added. Next connect the remaining local unification
witness dispatch, actual attached Split return invariants and tree/forest rank
to complete parent assembly, then discharge residuals and strictly replay.
The two pair-row result slots still lack checked protection; no payload was
removed to bypass that obligation. Next resident identifier: 2283.


## Complete local leaf-table checking — 2283–2289

The stronger leaf contracts now use the existing head, unification, fresh,
reflexive, pair and ordinary witness dispatch. `lpp_check_leaf_control` checks
every retained action and its coverage together with the complete established
source table. Its theorem retains initial knowledge, finiteness, leaf invariant,
residual termination and all nonempty boundary contracts as explicit premises.
Absent actions cannot discharge Split obligations.

Fourteen lemmas pass resident Isabelle without oracles/skipped proofs, including
missing row/context/witness and orphan witness rejection. Diagnostic generation
first failed because nested set union demanded an operational-goal comparison
instance (2288, 49.614 seconds). Proved equivalent finite-list traversal code
equations fix this without changing the check; export 2289 took 47.796 seconds.
Only this diagnostic module was generated; the unified checker is unchanged.

Fresh original and renamed source exports each pass all 38 retained source and
separation action checks and all five local tables for slot 0. Each rejects 15
invalid return-slot checks, two missing-pair-separation mutations and 15 table
mutations. The pair-row slot 2 remains unprotected; region 19's slot 2 is outside
its return arity. The full payloads and interfaces remain intact. Evidence and
hashes: `target/prolog-leaf-table-2288/`; native source exports: Ferrum
`target/prolog-leaf-table-2738/`. No native rebuild was needed.

These are actual local table checks, not root certificates or attached-caller
return proofs. Slot 0's local success does not establish the caller-tail contract.
Next bind the initial invariant, actual Split interfaces and attached return
facts to the tree/forest rank, finish parent assembly and residual discharge,
and perform strict replay with two unified checks. No new root verdict.
Next resident identifier: 2290; native evidence: 2739.


## Actual attached return-slot transport — 2295

`LP_Prolog_Attached_Return_Leaf` connects actual continuation coverage to numeric
return slots. It proves that a fresh body variable is separated from any finite
observed caller value covered by the actual MGU's continuation. The matching
specialization preserves the caller leaf effect and acquires separation using
the same MGU, including callers absent from the selected atom.

The actual attached base-step theorem preserves the full leaf stack through
matching resolution and its alternative cases. Attachment leaves every saved
frame's own environment intact. An executable slot-occurrence check has a
soundness lemma and positive/missing-slot/missing-continuation controls. The
continuation is required; no isolated-helper coverage premise is invented.

Nine lemmas pass without oracles/skipped proofs. Receipt and source hash:
`target/prolog-attached-return-leaf-2295/`. Final check took 3.763 seconds.
Attempt 2293's reverse invariant rewrite was interrupted after 20.813 seconds;
an explicit attached-invariant fact fixes it. Other corrections concerned the
runtime support map and the shared cut-symbol signature. The resident was
preserved; no native/full rebuild or checker export.

Next transport these actual caller-slot facts through normalized univ and nested
helper calls, then connect the complete attached invariant to the actual Split
interfaces/rank and discharge parent residuals. Existing source-variable univ
lemmas alone do not instantiate numeric caller return slots. No root gain;
next resident identifier 2296, native evidence identifier remains 2739.


## Normalized univ on actual return slots — 2307

A proof-only template reindexing bridges numeric return slots to the established
string-template univ theorem. Evaluation and variable support are proved exact,
and distinct slots cannot collide. Runtime terms, actual MGUs, clause variables,
source states and graph contexts are unchanged.

The shared MGU continuation-subset lemma projects a consequence of the same
actual unifier. This permits the attached univ theorem to retain arbitrary helper
pending goals alongside the caller continuation. Both actual unifications
preserve protected live return-slot leaf effects; the full-stack version keeps
saved alternatives' environments. It does not delete goals from execution.

An actual pair-MGU counterexample binds an observed output to a nonground
constructor and violates the ground-leaf contract. The separation premise is
therefore material even with finite inputs and live continuation coverage.
Twelve lemmas pass without oracles/skips; receipt/hashes:
`target/prolog-return-slot-univ-2307/`. Univ checks in 3.302 seconds, controls in
1.452 seconds. Failed development attempts and two interrupted automation
attempts (37.935/19.877 seconds) are recorded; explicit instantiation/type
annotations fix them. The hot resident was retained, with no native/full rebuild
or checker export.

Next complete attached invariant preservation through the remaining operations
and nested helpers, bind both actual Split interfaces to the return rank, and
finish parent residual/source certification and strict replay. No source verdict
added. Next resident identifier 2308; native evidence remains 2739.


## Checked heads and actual forest continuation — 2317

The existing matching, anchored and proper-spine head witnesses now provide
actual successful resolution effects for arbitrary pending caller goals.
Attached ground equality and resolution preserve caller leaf facts in their
own numeric return environment, retaining failure alternatives. Proper-spine
matching does not assert finite elements; finite-call premises stay explicit.

The forest composition theorem connects actual returned-tail observations to a
strictly smaller forest call. It uses the shared attached-call semantics and
retains initial invariant, every reachable attached step, saved alternatives,
prefix termination and lower continuation obligations. It is a conditional
composition theorem, not a completed module or root certificate.

Eight lemmas pass without oracles/skipped proofs. Evidence and source hashes:
`target/prolog-attached-forest-2317/` in the CeTA checkout. Ground, resolution,
checked-head and composition checks took 3.331, 2.486, 0.757 and 1.346 seconds.
Composition attempts exposed an unconstrained sum type; explicit tree/forest
types fix it. No native/full rebuild or unified export. Baseline remains
**90 YES + 97 NO + 34 UNKNOWN**; no new root gain.

Next discharge the complete attached invariant and initial observations against
both established Split interfaces, finish parent residual/source assembly and
strictly replay with two unified checks. Resident session is preserved; next
resident identifier 2318, next native evidence identifier 2739.


## Actual payload initialization coordinates — 2319 / 2739

The checked interface-slot predicate requires an in-bounds payload entry equal
to the observed source term. Its evaluation theorem connects that source value
to the numeric return environment. The stack initialization theorem requires
observations for every saved frame and tracked slot, not just the active frame.
Missing slots cannot use the return environment's default constant as evidence.
Six lemmas, including missing/wrong-slot controls, pass in 0.331 seconds without
oracles/skipped proofs. CeTA evidence: `target/prolog-leaf-initialization-2319/`.

Ferrum's forest binding now checks the same tail coordinate in both the prefix
and continuation payloads. The existing generalized Split regression passes
with missing-payload and mismatched-return mutations. Incremental native build:
22.43 seconds. Fresh original and renamed source inspections pass in 2.320 and
2.288 seconds: Split 30 has tail slot 2; Split 44 has tail slot 1. Source/binary
hashes and logs are retained in Ferrum `target/prolog-leaf-initialization-2739/`.
These inspect actual established graphs; no graph contexts or payloads changed.

This supplies checked coordinate initialization premises, not initial finite
observations or the complete reachable-step invariant. Those remain required
before parent assembly, residual discharge and strict source replay. No unified
export or full rebuild; no root gain. Baseline remains 90 YES + 97 NO.
Next resident identifier 2320; native evidence 2740.


## Actual arithmetic and term-test preservation — 2324

Four lemmas now cover scalar arithmetic and term tests directly on the shared
answer machine, including arbitrary caller environments and attached pending
goals. Arithmetic success uses the existing stable evaluator's bounded atomic
substitution, covering its integer and binary64 interpretations. Failure, error,
saved alternatives and unsupported-domain self-loops remain in the relation.
An invariant preserved by a self-loop is not a termination proof.

Resident verification passes in 0.542 seconds without oracles/skipped proofs;
receipt/hashes: CeTA `target/prolog-attached-arithmetic-2324/`. Early attachment
applications needed explicit map normalization. No native/full rebuild or unified
export. Baseline remains 90 YES + 97 NO; no new root certificate.

The remaining assembly obligations are distinct:

| Operation or interface | Available proof | Still required for the root |
| --- | --- | --- |
| Actual payload slots | Checked equality and bounds; original/renamed Splits 30:2 and 44:1 | Initial finite tree/list observations |
| Resolution and ground equality | Actual attached-step preservation from checked heads/source facts | Reachable source contexts and caller coverage at each use |
| Arithmetic and term tests | Actual answer-step preservation with arbitrary pending goals | Reachable dispatch coverage and termination/domain obligations |
| Normalized univ | Two-actual-MGU caller-slot preservation | Intermediate-state invariant and fresh-output separation transport |
| Nested helpers | Conditional actual-return forest composition | Complete dependencies, invariant preservation and rank/interface binding |
| Parent residual | Nine diagnostic children previously checked | Remaining child and complete original-source assembly/replay |

Next focus on the normalized-univ intermediate states and propagation of caller
separation from fresh clause variables. Do not replace this obligation with a
macro proof that assumes its intermediate facts. Next resident identifier 2325;
native evidence identifier remains 2740.


## Attached pair intermediate preservation — 2327

The first reflexive MGU now yields a common inverse on the pending pair and
an observed numeric caller slot, with arbitrary helper pending goals retained.
Finite inverse transport preserves the caller observation, finiteness of the
pair RHS, pair separation and caller protection at the intermediate state.
The stack theorem preserves every observed slot and leaves saved environments
unchanged. It does not assume the reflexive MGU itself is identity.

Three lemmas pass in 2.279 seconds without oracles/skipped proofs; receipt and
hashes are in CeTA `target/prolog-attached-intermediate-2327/`. An initial proof
needed explicit slot specialization before simplifying the coordinate name.
No native/full rebuild or checker export. Baseline remains 90 YES + 97 NO;
no source verdict added.

The algebraic intermediate-state transport is now available. The remaining
source connection must initialize its separation from fresh clause variables,
identify each actual reachable univ normalization transition and dispatch the
second pair step with these transported facts. Full caller-invariant coverage,
initial observations, nested Split assembly and parent residual discharge are
still required before original-source certification and strict replay.
Next resident identifier 2328; native evidence remains 2740.


## Checked head acquisition of caller separation — 2328

The existing checked matching, anchored and proper-spine head witnesses now
establish caller leaf preservation and separation from any fresh body variable
in the actual successful resolution. Source knowledge/context and numeric caller
return environments remain distinct. The ground-head case uses finite ground
transport; neither ordinary groundness nor a proper spine alone implies finite
elements. Actual continuation coverage and finite-call/rest premises remain.

The theorem passes in 0.524 seconds without oracles/skipped proofs, recorded in
CeTA `target/prolog-checked-caller-2328/`. No native/full rebuild or unified
export. This closes the checked-head acquisition step needed before univ's
intermediate separation transport; it does not itself enumerate reachable
states or establish all later substitutions preserve those facts.

Next connect acquisition and intermediate pair preservation to the actual
reachable source dispatch, including both fresh outputs and failure branches,
then complete nested Split invariants, parent residual discharge and original
source replay. Baseline remains 90 YES + 97 NO; no root gain. Next resident
identifier 2329; native evidence remains 2740.


## Fresh pair output acquisition — 2330

The checked fresh-decomposition predicate and checked head witness now jointly
produce both actual runtime output variables, their distinctness, separation
from the decomposition input and separation from the caller observation.
The caller leaf effect is preserved. Actual resolution, source context,
continuation coverage and finite resolved-call premises remain explicit.

Native inspection confirms `FreshClauseView::discover` requires distinct
body-only outputs and univ as the first clause goal; `NormalizedSeparationTrace`
retains resolution/univ/reflexive/pair links and incoming-edge coverage. No new
native dispatch or benchmark-specific rule was introduced. Connecting those
traces to this caller-parameterized theorem remains an assembly obligation.

One new lemma plus its predecessor pass in 0.603 seconds without oracles/skips;
evidence in CeTA `target/prolog-checked-pair-caller-2330/`. A reserved fact name
was corrected during development. No native/full rebuild or unified export.
No root gain: 90 YES + 97 NO. Next resident 2331; native evidence 2740.


## Checked resolution-to-univ caller path — 2332

The combined local path theorem uses checked head/fresh-decomposition witnesses,
actual clause resolution, source context and finite observations to derive
caller leaf preservation after both normalized unifications. All three actual
substitutions occur in order in the conclusion. Caller protection is derived
from resolution, rather than assumed as a separate path premise.

This is the successful local path only. Actual source routing to those MGU
states, failed alternatives, complete module dependencies and residual proofs
remain obligations. It does not convert a local successful path into a complete
return contract or a root termination proof.

The theorem passes in 1.212 seconds without oracles/skipped proofs; evidence:
CeTA `target/prolog-checked-univ-path-2332/`. A substitution identifier needed an
explicit type to avoid an imported constant. No native/full rebuild or unified
export. No source gain; baseline 90 YES + 97 NO. Next resident identifier 2333;
native evidence remains 2740. Continue with complete trace dispatch and nested
Split assembly, followed by parent residual discharge and strict source replay.


## Actual univ builtin caller preservation — 2334

The existing `lpp_univ_decompose_outcome` requires a successful unifier to be
most general for every continuation. Instantiating this quantified premise with
an observer goal proves caller leaf preservation for fresh separated outputs.
The observer is a logical proof context, not an inserted source goal or a new
operational rule. No semantics or established graph is changed.

The full shared-domain step theorem covers success, failure, errors and saved
alternatives with arbitrary pending goals. A separate variable-input step
preserves the invariant under the existing error/domain envelope. Unsupported
self-loops are retained and still prevent a termination proof; invariant
preservation does not discharge the domain obligation.

Three lemmas pass in 0.627 seconds without oracles/skipped proofs; evidence:
CeTA `target/prolog-actual-univ-2334/`. No native/full rebuild or unified export.
This supplies direct actual-step preservation alongside the normalized source
path proof. Next use checked fresh-clause acquisition to discharge its runtime
premises throughout reachable helper execution, finish nested Split/rank
assembly and parent residual discharge, then strictly replay the source result.
No root gain; baseline 90 YES + 97 NO. Next resident 2335; native evidence 2740.


## Checked fresh clause to actual univ step — 2336

The checked clause/head acquisition now discharges caller-protection premises
of the actual univ step for every tracked slot. Constructor argument finiteness
is derived from the finite resolved head and checked input occurrence. Variable
inputs use the existing variable-domain step theorem. Actual resolution,
source knowledge/context and caller continuation coverage remain bound.

The post-resolution stack invariant remains explicit, including saved frames;
no successful-call facts are transferred to resumed alternatives. The preceding
checked resolution step theorem supplies this invariant once actual successor
routing is established. Complete reachable-state coverage and nested helper
assembly remain open.

Verification passes in 2.625 seconds without oracles/skips; evidence is CeTA
`target/prolog-checked-fresh-step-2336/`. One redundant proof method was removed.
No native/full rebuild or unified export. No root gain: 90 YES + 97 NO.
Next resident 2337; native evidence 2740. Continue with complete source routing,
Split invariants/rank assembly and residual discharge before strict root replay.


## Checked instance transport of attached leaf invariants — 2337

The shared return-link soundness theorem now transports the attached caller
leaf invariant across instance substitution and scope renaming. Its equality
covers the whole annotated stack and every payload, including saved frames.
The child knowledge facts and residual dependency edge remain explicit outputs.
No context is emptied and no saved environment is replaced.

One theorem with three conclusions passes in 0.240 seconds without oracles or
skipped proofs. Evidence: CeTA `target/prolog-attached-leaf-link-2337/`. This
transports an existing invariant; it does not establish initial observations,
prove a child residual or permit omission of a module dependency.

No native/full rebuild or unified export; no root gain. Baseline 90 YES + 97 NO.
Complete reachable helper coverage, nested Split/rank assembly and the parent
residual remain necessary before strict source replay. Next resident identifier
2338; native evidence identifier 2740.


## Caller-only observation gap confirmed — native 2740

Fresh original and renamed inspections show that both Split tails contain V3,
while their helper execution bindings cover only V0, V1 and V2. Split 30 retains
V3 at caller payload slot 2; Split 44 retains it at slot 1. Both complete caller
payloads remain intact. `ForestReturnBinding::caller_only_tail_variables` now
exposes observation variables absent from helper entry bindings, with a targeted
regression. This is syntactic interface coverage, not runtime non-sharing.

The result limits the applicability of the checked return-link leaf theorem:
it transports observations already present in the annotated link interface.
It cannot introduce the caller-only tail into an isolated helper payload.
Likewise, the earlier local-table slot 0 checks are not proofs about that tail.
The required assembly must carry the caller observer through a parameterized
attached execution contract, retaining the complete module and caller contexts.
Do not substitute a same-numbered helper slot or reset contexts to bypass this.

Incremental native build took 18.66 seconds; the generalized Split regression
passed in 0.10 seconds. Original/renamed inspections passed in 2.318/2.308
seconds. Evidence and hashes: Ferrum `target/prolog-caller-coverage-2740/`;
build log `target/prolog-caller-coverage-build-2740.log`. No CeTA code/export or
unified executable change. No root gain: 90 YES + 97 NO.

Next implement the attached-observer module-entry connection using the actual
step preservation proofs; then complete nested Split/rank assembly, residual
discharge and strict source replay. Next native evidence 2741; resident 2338.


## Attached observer module entry — 2341

The existing instance checker now supplies an entry theorem that instantiates
helper executable goals while retaining an arbitrary independent caller return
environment and the exact saved stack. Caller-only observations need not occur
in the helper payload or binding domain. This addresses the interface mismatch
confirmed at both actual Splits without changing graph contexts or payloads.

The contract-transfer theorem requires an attached-execution helper contract;
it does not derive one from isolated helper termination. Entry equality alone
also establishes no leaf effect or continuation termination. Scope permutations
are not included in this single-goal-frame entry specialization (empty swaps).

Two lemmas pass in 0.284 seconds without oracles/skipped proofs; evidence:
CeTA `target/prolog-observer-entry-2341/`. Development corrections involved
explicit valuation types and an imported identifier. No native/full rebuild
or unified export. Baseline 90 YES + 97 NO; no new root certificate.
Next assemble the parameterized attached-helper contract from actual-step
preservation and complete source dispatch, then nested Splits/rank and residual
proofs. Next resident 2342; native evidence 2741.


## Native attached-observer entries — 2741

`Modules::attached_observer_entry` reconstructs the exact helper entry from its
retained local table and checks the proposed source instance bindings against
the Split prefix goals, ground facts and guards. The receipt retains the full
Split interface independently of the helper execution state. Validation freshly
reconstructs it, rejecting removed caller payloads, helper goals and bindings.
The generalized Split regression passes all these controls.

Fresh original and renamed inspections pass both entries: Split 30 to module 0
retains caller arity 4; Split 44 to module 47 retains caller arity 3. Their helper
bindings still cover V0/V1/V2 only. Caller V3 is retained independently, not
silently added to the isolated helper payload. No graph contexts are reset.

Incremental build: 33.65 seconds; regression: 0.10 seconds; source inspections:
2.322/2.290 seconds. Evidence/hashes: Ferrum `target/prolog-observer-entry-2741/`,
build log `target/prolog-observer-entry-build-2741.log`. The only post-build
source edit moved an existing documentation comment to its intended method.

These are reconstructed entry premises, not an attached helper proof or a root
certificate. The native receipt still needs certificate serialization/checker
integration together with the complete parameterized helper contract and all
residual children. No CeTA code/export or unified executable change this turn;
no root gain, baseline 90 YES + 97 NO. Next native evidence 2742; resident 2342.


## Serialized observer-entry instance checks — 2342 / 2742

The ignored native inspector now exports each observer entry's caller node,
helper node, instance bindings and complete caller return state through the
shared serializers. The existing Isabelle-generated diagnostic module already
exports `lp_cut_check_instance` and the parsers; no code generation was needed.
A separate harness parses the receipts and invokes that generated checker.

Original and renamed sources each pass both entry checks and reject eight
mutations: missing helper goals, missing caller goals, invented ground facts
and wrong instance bindings for each Split. Caller payload arities 4/3 and goal
alignment are checked separately by the harness. These arities are external
regression expectations, not production dispatch. This verifies the exact
instance premise; it is not a unified root certificate or complete parent proof.

Native evidence: Ferrum `target/prolog-observer-xml-2742/`; generated-checker
harness/logs/hashes: CeTA `target/prolog-observer-check-2342/`. Incremental build
29.49 seconds; generalized regression 0.10 seconds; original/renamed export
2.279/2.289 seconds. One Rust module path and one tool executable path were
corrected; failed logs are retained. No full rebuild, checker regeneration or
unified executable change. Baseline stays 90 YES + 97 NO; no source gain.

Next discharge the complete parameterized attached-helper contract, integrate
it with nested Split/rank assembly and parent residual proofs, then perform
strict original-source replay. Next native evidence 2743; resident 2343 (2342
identifies the standalone checker diagnostic, not an Isabelle theory load).


## Complete attached-observer dependency receipts — 2743

`attached_observer_dependencies` traverses the retained module graph from each
helper entry. It retains exact local regions, contexts, Split interfaces,
boundary references and original source identity. Each reachable Split requires
both prefix and continuation targets. Cycles remain references, not proofs.
A boundary marked by a source region must have a dependency entry; removing it
causes reconstruction failure. Fresh validation rejects omitted regions,
Splits and boundaries in a receipt.

Original and renamed inspections agree. Split 30 requires local modules
0/19/28/35/47, Splits 30/44 and seven boundary links. Split 44 requires modules
19/28/35/47, Split 44 and four links. These populations are obligations for the
parameterized caller contract; neither graph reachability nor closed construction
establishes their termination or returned-value contracts.

Incremental build 37.58 seconds; generalized regression 0.12 seconds;
original/renamed inspection 2.309/2.286 seconds. Evidence/hashes: Ferrum
`target/prolog-observer-dependencies-2743/`; build log
`target/prolog-observer-dependencies-build-2743.log`. No CeTA proof/export or
unified-checker change. No root gain: baseline 90 YES + 97 NO.

Next assemble checked local preservation and recursive Split return/rank
obligations over these complete referenced populations, then discharge parent
residuals and strictly replay the source certificate. Next native evidence 2744;
resident identifier remains 2343.


## Synchronized helper and caller observations — 2350 / 2744–2745

The shared resolution projection already exists in `LP_Cut_Return_Sequence`;
no new MGU semantics or duplicate projection rule was needed. The new
`LP_Prolog_Attached_Observer_Product` uses the existing answer instrumentation
and interface reflection to retain both helper and caller observations on one
execution. Every active attached caller step lifts to a combined-interface step,
reflects to a helper-prefix step, and projects to the helper's original answer
semantics. The caller projection is exactly the actual successor. Both
projections therefore use the same underlying execution, including saved
alternatives, cuts, failure, builtin errors and unsupported-domain self-loops.
No runtime nonsharing or termination claim is inferred from interface separation.

The theory also proves caller leaf-invariant projection and that concatenating
finite helper/caller payloads satisfies both existing return-projection checks.
Nine theorem conclusions checked in the retained Isabelle process in 0.633s,
without skipped proofs or oracles. Evidence and failed-attempt classifications:
CeTA `target/prolog-observer-product-2350/`; earlier successful step receipts are
retained in `target/prolog-observer-product-2349/`. No checker generation or
full rebuild was performed.

Native `attached_observer_product` binds the complete helper payload through
the checked entry substitution, concatenates it with the independent caller
payload, and retains both projections. Unbound helper observations reject
construction. It preserves runtime variable sharing; it does not rename shared
values or reset contexts. On original and renamed numbervars, Split 30 retains
helper coordinates `[0,1,2]` and caller `[3,4,5,6]`; Split 44 retains helper
`[0,1,2]` and caller `[3,4,5]`. The caller-only tail remains represented in both.
Native evidence is Ferrum `target/prolog-observer-product-2744/`; original and
renamed graph checks took 2.299s and 2.308s. The incremental native build took
35.63s and the generalized fixture passed in 0.12s. Additional controls retain
shared values and reject an unbound helper payload, missing payloads, missing
projections and swapped projections; their log is
`target/prolog-observer-product-controls-2745.log`.

This closes the synchronization/interface-representation subproblem, not the
parameterized helper contract. Next, connect the helper projection to each
checked local row/context transition, prove the caller invariant on the actual
combined step, and cover every referenced boundary and nested Split. The full
source/rank assembly and residual discharge remain required. Certified totals
remain 90 YES + 97 NO; the unified CeTA executable is unchanged.


## Checked row links with independent caller observations — 2356

`LP_Prolog_Observer_Row_Link` connects the synchronized observation interface
to existing checked graph links. The helper projection supplies the exact
annotated source row; its checked target reconstructs the combined runtime
stack with the actual caller projection, frame by frame. Caller-only values
never need to occur in helper bindings. Complete frame alignment is required:
a missing saved frame cannot pass, and a stale saved caller environment still
violates the leaf invariant even when the active environment satisfies it.

The context-link theorem reuses `lpp_separation_functor_link_sound` and carries
all existing groundness/guards, freeness, stable arithmetic observations,
functor facts and separation conditions to the same target valuation. Scope
renaming commutes with interface projection. Caller invariance is transported
through the link; preservation by the preceding source operation remains a
separate premise, not a conclusion manufactured from helper termination.

11 theorem conclusions checked in the retained Isabelle process in 0.750s,
without skipped proofs or oracles. Evidence, hashes and failed proof attempts:
CeTA `target/prolog-observer-row-2356/`. No native code changed and no rebuild,
checker generation or unchanged residual search was run. Source certification
of numbervars remains open, and totals stay 90 YES + 97 NO; the unified checker
is unchanged. Next connect actual local action steps to this successor-context
interface, then assemble the complete recursive dependency population and rank.


## Actual resolution and ground-equality observer steps — 2360–2361

`LP_Prolog_Observer_Resolution` and `LP_Prolog_Observer_Ground_Equality` now
combine actual attached execution with existing source-row context proofs and
caller leaf preservation. Each conclusion supplies the same joint successor,
its exact caller-result projection, a strict residual path, the helper's next
checked context (including separation), and the preserved caller invariant.
The helper and caller conclusions cannot come from different executions.
Success and failure transport obligations remain separate. Clause selection
and equality retain their original source semantics and saved alternatives.

Resolution consumes the existing checked head witness; ground equality uses
ground facts from the current checked node/context. Neither treats groundness
as integrality. Finite call/continuation observations and live caller-slot
coverage remain explicit premises. These lemmas do not infer finiteness from
an arbitrary rational term or discharge a recursive module by themselves.

Four theorem conclusions passed in the retained Isabelle process without
oracles or skipped proofs. Resolution took 1.247s; ground equality 1.204s.
Evidence, source hashes and failed-attempt classifications are in CeTA
`target/prolog-observer-actions-2361/`. No native rebuild, checker generation or
unchanged residual campaign was run. The unified executable remains unchanged.

Remaining work is to lift the other local actions into this same synchronized
interface, retain finite observations and fresh-output separation across their
steps, then assemble the complete nested Split contracts and forest rank.
Numbervars remains unproven; certified totals remain 90 YES + 97 NO.


## Shared observer-step composition and ordinary actions — 2363–2369

`LP_Prolog_Observer_Step` provides one composition rule for the existing helper
source simulation and caller preservation on the same actual successor. The
rule retains the helper's related residual subject, target context, scope
renaming and the caller's leaf invariant. It does not infer either local premise
from termination, and does not discharge recursive module dependencies.

`LP_Prolog_Observer_Term_Test` instantiates this rule with the existing checked
term-test/domain proof and actual caller-invariant preservation. The control
lifting in `LP_Prolog_Observer_Control` reuses builtin exclusion and active-prefix
attachment; `LP_Prolog_Observer_Checked_Control` instantiates it for checked
administrative and clause-selection actions. Empty target separation conditions
are checked where those existing rules require them; incoming contexts and
saved environments are not reset. Exhausted helpers cannot use the control
rule to execute their suspended caller because active-prefix coverage is an
explicit premise.

Eight theorem conclusions pass without skipped proofs or oracles. Retained
resident checking took 0.353s for shared composition, 0.667s for term tests,
1.911s for generic control, and 1.004s for checked control. Evidence/hashes and
failed-attempt classifications: CeTA `target/prolog-observer-control-2369/`.
An overly broad elimination proof was interrupted after 31.567s and replaced
with explicit list/frame cases; the Isabelle resident was preserved. The frame
shape lemma uses an explicit generic frame name, avoiding an imported constant.
No native rebuild or checker generation was needed.

The remaining source assembly includes arithmetic/univ normalization, finite
observation and separation transport, and recursive Split return/rank contracts.
Numbervars remains unproven. Certified totals stay 90 YES + 97 NO; the unified
CeTA executable is unchanged. These checked source-step families are not counted
as benchmark gains.


## Attached arithmetic normalization contract — 2372

`LP_Prolog_Observer_Arithmetic_Normalization` exposes the existing checked
`is/2` normalization as an exact helper context witness, then composes it with
an independent caller observation. The normalized equality has the same active
and saved environments as the actual source call. The checked child valuation
supplies the residual descent, ground/guard knowledge, freeness, stable
arithmetic context and functor observations. Caller leaf invariance holds at
normalization because its observation environments have not changed; actual
equality substitution remains the child's checked obligation.

The new attached contract requires the normalized child's complete answer
contract. It reuses `lpp_univ_evaluation_domain_contract` to cover actual `is/2`
execution, including errors and failed equality, with the fixed source-domain
and stable-operation premises. No integer-only restriction is introduced and
no return contract is inferred from termination alone. The caller environment
is not rebuilt through the helper's fresh result-variable assignment.

Two theorem conclusions pass without skipped proofs or oracles in 0.686s of
retained-process checking. Evidence/hashes and the failed proof attempt are in
CeTA `target/prolog-observer-arithmetic-2372/`. No native rebuild or checker
generation was performed. The next normalization obligation is univ's
reflexive-plus-pair equality, with its initialized separation and exact child
context; recursive Split/forest-rank assembly remains outstanding.
Numbervars remains unproven, totals stay 90 YES + 97 NO, and the unified checker
is unchanged.


### Attached univ normalization — 2026-11-18

The checked observer univ witness now exposes the exact normalized child
valuation, residual edge, ground/guard knowledge, freeness, arithmetic context,
functor facts and initialized separation together. The attached univ contract
uses that witness with the caller's independent observation environment and
saved alternatives. Both normalized equalities remain in the child contract;
the existing reflexive-equality theorem justifies its normalization step.
Actual univ coverage and domain premises remain explicit, including variable
input error behavior. Termination alone does not discharge the return contract.

CeTA `LP_Prolog_Observer_Univ_Witness` and
`LP_Prolog_Observer_Univ_Contract` pass in the retained Isabelle process with no
oracles or skipped proofs. The witness check took 1.206 seconds; the final
contract check took 1.068 seconds. Receipts, source hashes and failed-attempt
classifications are in CeTA `target/prolog-observer-univ-2383/`.
No native build or unified checker generation was required.

Next are actual equality substitution and finite-observation/separation
transport, followed by recursive Split/forest-rank assembly and native/unified
integration. Numbervars remains unproven. Certified totals remain 90 YES +
97 NO; this proof development is not a new source certificate and does not
change the installed unified checker.


### Actual attached univ equality transitions — 2026-11-18

`LP_Prolog_Attached_Univ_Equality_Steps` now applies the caller leaf contracts
to actual answer-machine transitions. The reflexive step preserves the caller
observations for arbitrary MGUs on the complete pending continuation. The
normalized univ two-step theorem retains both actual substitutions, and covers
saved-alternative restoration on equality failure. A domain-aware wrapper
connects the result to the source transition relation. Fresh output variables,
finite arguments, caller separation and live return-slot coverage are explicit
premises; they still require discharge at the graph rows.

Integration exposed a concrete defect in the earlier
`lpp_attached_pair_intermediate_stack` and
`lpp_attached_normalized_univ_leaf_stack`: the name `entry` resolved to an
imported constant with function type, so their checked statements could not
instantiate real execution stacks. Both now use the general variable
`frame_entry`. Their dependent theories were rechecked incrementally in the
retained Isabelle process. The new actual-transition theorems exercise the
previously unusable instantiations.

Five main theorem conclusions and three return-slot controls pass without
oracles or skipped proofs. Equality checking took 1.275 seconds; controls took
1.533 seconds. The unprotected-output counterexample still proves that a
caller leaf can become a nonground constructor when separation is absent.
Evidence and failure classifications are in CeTA
`target/prolog-observer-equality-2393/`. Prior receipts remain historical;
the two corrected source hashes are bound by this new receipt.

No native rebuild or unified export was performed. Next are graph-row transport
of finite observations and caller separation, trim/parallel boundaries, and
recursive Split/forest-rank assembly before native integration and strict root
replay. Numbervars is still unproven; totals remain 90 YES + 97 NO and the
installed unified executable is unchanged.


### Checked observer trim and parallel boundaries — 2026-11-18

`LP_Prolog_Observer_Boundary_Contracts` and
`LP_Prolog_Observer_Checked_Boundaries` connect caller-attached answer contracts
to the established graph's actual Trim and Parallel actions. Exact helper
projection determines the runtime prefix/suffix or indexed frame. The caller's
observation environments are retained from those actual frames; they are not
reconstructed from helper substitutions.

Trim only drops the suffix proved to consist of barriers. Parallel assembly
requires a complete attached answer contract for every source frame, including
saved alternatives. The existing checked links transport all source context
facts and explicit separation evidence. Unlike the earlier empty-target
boundary rule, these contracts can retain nonempty separation contexts when
the existing transport checker validates them. Each lower contract is still a
full answer contract, and strict residual reachability links its subject to
the parent's subject. No helper termination result substitutes for it.

Eight new theorem conclusions and four existing negative controls pass without
oracles or skipped proofs. The controls cover missing alternatives, missing
context rows, trimming a nonbarrier, and stale saved caller observations.
Assembly checked in 0.931 seconds and the two source-action contracts in
1.013 seconds using the retained Isabelle process. The receipt and source
hashes are in CeTA `target/prolog-observer-boundaries-2403/`.

Finite-observation and fresh caller-separation transport through the local
rows, recursive Split/forest-rank assembly, native integration and original-root
strict replay remain. No native build or unified export was performed;
numbervars remains unproven and certified totals remain 90 YES + 97 NO.


### Actual attached finite execution — 2026-11-18

`LP_Prolog_Checked_Attached_Finite` discharges finite resolved-head and
attached-continuation obligations using the existing separation-head checker.
Matching, anchored-ground and observed-spine witnesses share the same proof.
The finite call is retained as an input premise: arbitrary rational unification
is not treated as finite. The combined resolution theorem preserves both
finite execution and caller leaf observations, including saved alternatives.
The fresh-univ caller theorem now derives resolved finiteness from that checked
head, eliminating the earlier explicit resolved-finiteness premise.

`LP_Prolog_Attached_Univ_Finite_Steps` proves finite intermediate and final
execution for the two actual normalized univ equalities. It uses their real
MGUs over the full attached continuation. The domain-aware combined theorem
also retains caller leaf observations. Distinct fresh outputs and caller
separation remain explicit; finite list spines are not substituted for finite
argument elements.

Six new conclusions and two existing controls pass without oracles or skipped
proofs. The controls demonstrate that finite helper execution alone does not
cover a suspended caller value, including values in saved alternatives.
Checked-head proofs took 0.684 seconds; final finite-univ proofs took 1.946
seconds. Evidence/hashes: CeTA `target/prolog-observer-finite-2407/`.
All four incremental proof loads succeeded without a native build or full
checker rebuild.

Remaining work is assembling these local invariants with graph context and
fresh-separation evidence, then recursive Split/forest-rank assembly, native
integration and original-root strict replay. Numbervars remains unproven,
certified totals remain 90 YES + 97 NO, and the installed unified checker is
unchanged.


### Observer parent assembly and caller scope restoration — 2026-11-18

`LP_Prolog_Observer_Table_Contract` assembles full caller-attached answer
contracts by the shared modular induction over certified residual subjects.
Each child supplies its own joint runtime stack, invariant and complete helper
module representation. Every represented local row and every boundary remains
an explicit node-contract obligation. Exhausted states have a proved terminal
case. A silent-step composition lemma connects actual local simulations to
these answer contracts. This theorem still requires residual termination and
all local/boundary contracts; it does not certify a root by itself.

`LP_Prolog_Observer_Attached_Scopes` restores a canonical graph contract to the
actual caller-attached state when the graph's selected scope renamings fix the
suspended continuation. Its negative control proves that renaming only the
helper is invalid when the caller contains an affected cut. No caller cut
scope is erased. Instantiating canonical local rules with this scope condition
and the finite/leaf invariant remains a required assembly step.

Seven theorem conclusions pass without oracles or skipped proofs, including
the caller-cut counterexample. Parent assembly checked in 2.184 seconds and
scope restoration in 0.291 seconds; receipts/hashes are in CeTA
`target/prolog-observer-table-2416/`. The pre-break resident session was verified
live and reused; no rebuild or process restart was required.

Numbervars remains unproven. Remaining work includes concrete observer node
contracts, recursive Split/forest-rank assembly, residual discharge, native and
unified integration, and original-source strict replay. Certified totals remain
90 YES + 97 NO, and the installed unified checker is unchanged.


### Canonical observer node bridge — 2026-11-18

`LP_Prolog_Observer_Canonical_Node` proves that continuations with no cut or
expansion scopes are fixed by every graph scope renaming. It lifts canonical
local contracts to the observer table's scope-aware node contract, provided
the joint invariant is preserved by scope renaming. Complete lower contracts
and all source context facts remain explicit. This discharges a shared scope
side condition for scope-free continuations, rather than changing any source
cut semantics. The affected-caller-cut counterexample is retained as a control.

Two new conclusions plus that existing control pass without oracles or skipped
proofs in 0.604 seconds. Receipt/source hashes are in CeTA
`target/prolog-observer-canonical-2417/`. No native or checker rebuild was run.
Numbervars still needs concrete local node instantiations, recursive Split
assembly, the remaining residual, integration and strict replay.

The new goal also requests a grouped overview of all remaining gaps. Ferrum
`docs/prolog-remaining-gaps.md` and its JSON inventory cover all 34 unresolved
roots exactly once, binding the pinned 90 YES + 97 NO campaign to the historical
finite-direct diagnosis. Its 25 Split, six module, two local-step and one parser
groups are explicitly historical first failures, not claims about established
SEG closure or future verdicts. The inventory must be refreshed after a gain.


### Joint observer invariant — 2026-11-18

`LP_Prolog_Observer_Invariant` combines finite execution of the actual attached
caller state with leaf observations in all caller environments. It proves
scope stability for scope-free continuations and preservation under selecting
sub-stacks. A negative control excludes a nonfinite suspended value in a saved
alternative. The invariant supplies the scope premise of the canonical-node
bridge; finite helper goals alone still do not suffice.

Three conclusions checked without skipped proofs or oracles in 5.840 seconds;
receipts and source hashes are in CeTA `target/prolog-observer-invariant-2419/`.
No rebuild or new root certificate. Numbervars remains unproven; concrete node
instantiations, recursive Split/forest-rank assembly, residual discharge,
integration and strict replay remain. The 90 YES + 97 NO baseline and installed
unified checker are unchanged. The grouped remaining-root inventory is in
Ferrum `docs/prolog-remaining-gaps.md`.


### Checked observer ordinary-node assembly — 2026-11-18

The observer parent contract now has concrete Trim, Parallel, administrative
and clause-selection node instances. `LP_Prolog_Observer_Ordinary_Check` adds an
executable dispatch check and soundness theorem for these actions, terminal
states and inconsistent guards. Every ordinary link checks transport from the
actual incoming separation context to its target; nonempty facts are retained.
The shared simple-step contract preserves finite execution of the attached
caller and leaf observations in every saved environment through the actual step.
Exhausted helpers cannot enter the silent administrative rule. Arithmetic,
unification, resolution and univ retain their separate contract obligations.

The incremental resident check produced 15 trusted conclusions, including
nonempty transport, missing-initialization and missing-child controls, rejection
of exhausted-helper and unsupported arithmetic dispatch, and the retained
missing-frame and nonfinite-saved-environment controls. No oracles or skipped
proofs. Receipts and source hashes are in CeTA
`target/prolog-observer-ordinary-2430/`. Attempt 2429 caught an imported-name
collision in a test; the final test uses unambiguous row variables. No native,
export or unified-checker rebuild was performed.

This remains conditional source-proof infrastructure: numbervars is not yet
certified. Remaining work includes concrete special-action contracts, fresh
separation and finite initialization, recursive Split/forest-rank assembly,
the open residual, certificate reconstruction and unified integration, followed
by original-source strict replay and two checks. The pinned baseline remains
90 YES + 97 NO + 34 UNKNOWN; LP-cut remains 84 YES + 9 NO.


### Special observer nodes and caller-protection gap — 2026-11-18

Concrete observer parent contracts now cover resolution (matching, anchored and
observed-spine heads), checked fresh-clause separation acquisition, ground
equality and term tests. The existing unification checker is connected to these
contracts. Actual substitutions preserve the finite attached continuation and
caller leaf observations; failed branches retain their own context obligations.
The empty-target specialization requires already-empty target separation facts;
it does not clear an existing context. Fresh resolution retains checked nonempty
facts and normalization receipts.

A verified counterexample in `LP_Prolog_Observer_Protection_Control` shows why
these components do not yet suffice for univ/pair assembly: the finite-plus-leaf
invariant can hold while the caller aliases a helper output. A valid pair MGU
then turns that caller leaf into a nonground constructor, violating the promised
return relation. This is a counterexample to the proposed invariant sufficiency,
not to an exported checker rule or to numbervars termination. The existing
fresh-clause theorem proves the required caller separation, but assembly must
carry that acquired evidence to the subsequent univ/equality steps.

`LP_Prolog_Observer_Block_Contract` supplies a two-actual-step composition rule
that keeps acquired intermediate evidence scoped to that execution. Every
outcome must still be covered and the endpoint must satisfy checked residual
descent, full representation and the caller invariant. It is not yet the
concrete fresh-univ block certificate. Read-only inspection of original and
renamed saved tables identifies the same sequence in regions 0 and 47:
local 3 (fresh resolution), 6 (univ), 10 (reflexive equality), 13 (pair equality).
Ferrum `target/prolog-observer-block-diagnosis-2746/manifest.json` pins the tables,
all encoded targets and branch modes; no failure target was removed.

Seventeen conclusions, including the three-part protection counterexample and
retained missing-head, failure-context and return-slot controls, checked without
oracles or skipped proofs. CeTA `target/prolog-observer-special-2445/` retains
source hashes, receipts, timings and failed attempts. Only affected theories
were loaded in the resident process. No native or unified rebuild; no new root.
Next: instantiate the fresh-univ block with its real caller-separation evidence,
finish arithmetic/local assembly, then nested Split/forest descent and the open
residual, reconstruction, unified integration and strict replay. The baseline
remains 90 YES + 97 NO + 34 UNKNOWN and LP-cut 84 YES + 9 NO.


### Fresh-univ caller contract and equality simulation — 2026-11-18

The fresh-resolution/univ block now has a checked actual-execution caller
contract. It derives protection of caller leaves from the preceding resolution
MGU over the complete attached continuation, then preserves finite execution
and caller observations through the actual univ outcome. Intermediate caller
protection is derived, not assumed from the weaker finite-plus-leaf invariant.
The resulting contract still requires the block's source-graph descent and
representation, plus contracts for strict descendants.

Actual univ execution now connects to the normalized reflexive/pair equality
path. A new one-step simulation interface reuses the existing separation-aware
equality checks, preserves finite execution, and retains both success and
failure transports. Reflexive, separated-pair and ground-equality instances are
verified. Scope lifting preserves the complete module representation, and the
univ module block uses coverage of all represented equality nodes. This is a
conditional theorem: concrete graph coverage and the preceding resolution's
source simulation still have to be assembled. The existing native
`NormalizedSeparationTrace` supplies the candidate path and incoming-edge
receipts; no new graph, context reset or benchmark-specific rule was added.

Eighteen theorem conclusions passed the no-oracle/no-skipped-proof receipt in
`target/prolog-observer-univ-block-2466/`, with source hashes, available timings
and failed attempts retained. Only affected theories were loaded in the hot
resident process. Existing pair-check rejection lemmas remain dependencies of
the verified module block; no new certificate mutation or root replay is
claimed. No native/unified rebuild or new certified root. Remaining gates:
concrete source-block/parent assembly, arithmetic and nested Split/forest-rank
composition, the open residual, native reconstruction and unified integration,
then original-source strict replay with two checks. The pinned baseline remains
90 YES + 97 NO + 34 UNKNOWN and LP-cut 84 YES + 9 NO.


### Assembled fresh-univ source block — 2026-11-18

The fresh-resolution simulation now derives residual descent, finite helper
execution and full child representation using the existing checked separation
acquisition and normalization. The univ source-step theorem derives its domain
and initialization from the existing source-action and separation checks.
Scope lifting retains the complete representation and handles actual empty
results. The fresh-clause shape theorem establishes that the next actual state
is a univ frame; it does not assume away a failure branch.

`lpp_checked_fresh_univ_source_block` composes these steps under explicit
coverage of represented univ and equality nodes. The attached-caller theorem
`lpp_assembled_fresh_univ_observer_contract` now discharges the previous opaque
source-block premise and combines source descent with actual caller protection.
Its premises still require finite helper execution, finite attached caller
execution, exact helper projection, leaf-slot coverage, checked head and clause,
all incoming contexts and contracts for strict descendants. Neither termination
of a child alone nor the weaker caller invariant supplies those premises.

The next integration step must establish these coverage and initialization
premises from the actual graph receipts and connect the block to observer-table
assembly. In particular, the current observer invariant records finite attached
caller execution but does not explicitly record finite helper interfaces; that
additional premise must be justified or carried, not inferred silently. Remaining
work also includes arithmetic, nested Splits/forest descent, the open residual,
certificate reconstruction and unified export/replay.

12 conclusions passed without oracles or skipped proofs in CeTA
`target/prolog-observer-assembled-block-2482/`; the manifest retains hashes,
available timings and failed attempts. Only affected theories were loaded in
the live resident. No native/unified rebuild, new mutation campaign, original
root certificate or gain is claimed. Baseline: 90 YES + 97 NO + 34 UNKNOWN;
LP-cut: 84 YES + 9 NO.


### Checked block node and finite-helper clarification — 2026-11-18

The finite-helper concern in the preceding entry is resolved by proof, without
strengthening or resetting any state. `lpp_finite_execution` concerns goal stacks;
return-environment projection leaves those stacks unchanged. Removing the
attached continuation preserves finite execution. Thus the existing observer
invariant already implies finite helper execution, including saved frames.
This does not claim that arbitrary return-slot values are finite trees.

`lpp_observer_fresh_univ_node_contract` lifts the assembled block through the
existing canonical/scope interface. Its checked specialization derives matching,
fresh-clause acquisition and source simulation from the existing resolution and
separation checks. Five conclusions passed without oracles or skipped proofs;
CeTA `target/prolog-observer-block-node-2488/` pins receipts, source hashes,
incremental timings and failed attempts. No native or unified rebuild occurred.

The next issue is table assembly, not finite-helper initialization. The current
`lpp_observer_table_contract` requires an independent caller contract for every
local row. A checked fresh-univ block instead uses the acquired protection
across its internal rows; the earlier aliasing counterexample still prevents
claiming standalone contracts there from the weak invariant. Assembly must
recognize checked blocks, retain their internal edge/context checks, and cover
all exits and other incoming paths. The native `NormalizedSeparationTrace`
already records unique incoming edges and rejects internal module entries and
boundaries. Its proof integration remains required, alongside arithmetic,
nested Splits/forest descent, the open residual and original-source certified
replay. No new root: 90 YES + 97 NO + 34 UNKNOWN; LP-cut 84 YES + 9 NO.


### Proof frontier and checked block exits — 2026-11-18

Observer table induction now admits a proof frontier while retaining the full
original source table check. Internal rows are excluded only from the induction
representation; every initial and resumed state must have a frontier witness.
The restricted conditions retain all prior separation facts. An empty frontier
has no represented entry, and an external control row cannot be hidden by the
frontier-shape check.

General control-shape checks establish that actual univ outcomes leave the
internal univ/equality sequence. Success preserves the checked continuation
shape under its actual substitution; failure checks the saved alternative;
actual error outcomes are handled by the source semantics. Domain coverage
remains mandatory: unsupported-domain self-loops are not finite errors.
The checked exit theorem lifts through scopes and module representation and
composes with fresh resolution. The resulting attached-caller block contract
requires frontier contracts only at verified exits; it no longer assumes an
opaque semantic exit condition.

46 conclusions passed without oracles or skipped proofs, including 20 saved
control-state fixture conclusions from original and renamed helper regions 0
and 47. The fixtures retain XML goal-stack shapes and free sets; environments
are replaced by empty payloads only because these shape checks ignore them.
They are not full-state reconstruction or root certificates. Missing free-set
coverage is rejected. General controls also reject unknown continuation goals,
pending univ, and saved equalities. CeTA
`target/prolog-observer-frontier-2508/` pins input hashes, generator, fixture,
receipts, timings and failed attempts. No native/unified rebuild or fresh
campaign; no root gain.

Next: lift ordinary observer contracts with checked frontier destinations,
connect the frontier block contract to checked node dispatch, and validate
complete source-table coverage from the existing acquisition traces. Then
finish arithmetic and nested Split/forest descent, discharge the open residual,
and complete native reconstruction, unified integration and strict original
source replay. Baseline remains 90 YES + 97 NO + 34 UNKNOWN; LP-cut 84 YES + 9 NO.
