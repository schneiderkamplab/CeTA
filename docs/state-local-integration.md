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
