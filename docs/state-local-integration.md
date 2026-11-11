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
