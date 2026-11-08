---
type: Formal Specification
title: "TRS Relative: ranked signature review and guarded checking"
status: draft
---
# TRS Relative: ranked signature review and guarded checking

Read the [canonical specification and equivalence statements](trs-relative-specification.md)
and then [the concrete bridge](../thys/Category_Specifications/Relative_Integrated/TRS_Relative_Integrated.thy).
This review preserves the ranked semantics. It does not add a variable condition
to category validity or claim an unconditional signature-extension equivalence.

## TPDB conventions and the signature issue

The [TPDB category definition](https://termination-portal.org/wiki/Term_Rewriting)
allows arbitrary rule pairs, arbitrary starting terms, and full rewriting for
Relative. Rules may carry natural-number costs: zero is weak, positive is strict,
and omission is strict. Positive magnitudes do not affect relative termination.
There is no category-wide variable condition that discharges the old bridge premise.

Signature extension really can change relative termination. IsaFoR proves this
in `sig_ext_relative_rewriting_unsound` in
[Signature_Extension](../thys/Rewriting/Signature_Extension.thy). A concrete example
has only constants `a,b`, strict rule `a -> b`, and weak rule `a -> x`.
Every declared-signature sequence has at most one strict step: afterwards it is
at `b`. With an extra binary symbol, a weak step can preserve and replenish a
second branch while strict steps continue indefinitely. Direct CeTA checks
unrestricted terms and accepts a variable-condition-violation NO certificate
for this example. The original ranked-input gate must reject it. This is a
semantic mismatch between domains, not an unsoundness of CeTA's stated theorem.

Consequently, no proof can remove the extension premise from the existing
unrestricted NO theorem while preserving both semantics. The reviewed boundary
instead computes a sufficient condition from the original input:

- a declared symbol has arity at least two, including unused declarations; or
- every weak rule's right-side variables occur on its left side.

YES needs neither condition. When neither holds, the bound interface now accepts
a direct relative loop whose finite witness terms, substitution images and
one-hole context all respect the original declared signature. CeTA must still
check the loop, including an actual strict step. This closes the blanket input
exclusion for ranked loops without asserting the false extension theorem.
Other unrestricted NO proof forms still need the sufficient extension condition;
a rejected certificate is not a YES result or a completeness claim.

## Concrete theorem statements

`relative_no_guard F Ss` is the finite-input guard above.
`relative_no_guard_sound` derives `relative_extension_condition A S` from the
checked guard and exact signature/rule representation. `F` represents all of
`to_signature A`, not just symbols used in rules.

`trs_relative_integrated_YES` requires exact strict/weak rule lists and acceptance
by `certify_integrated_cert_problem False (Inn_TRS_input No_Strategy Rs Ss)
Termination (Decision True) certificate`. It concludes `trs_relative_terminates A R S`
without an extension premise.

`relative_bound_accepts F Rs Ss b certificate` requires concrete checker acceptance
with certificate assumptions disabled and, for NO, either the extension guard
or `relative_ranked_certificate F certificate`. The latter identifies a direct
loop and checks `ranked_relative_loop_guard`. The finite witness requirements
imply closure of every iterated context/substitution instance, proved in
[`TRS_Relative_Ranked_Loops`](../thys/Category_Specifications/Relative_Integrated/TRS_Relative_Ranked_Loops.thy).
`ranked_check_rel_loop_sound` proves ranked relative nontermination directly;
`relative_integrated_ranked_loop` connects it to concrete checker acceptance.
`trs_relative_bound_decision` assumes `relative_problem A R S`, exact representation
of signature and both rule lists, and this bound acceptance. Its conclusion is
`b` iff `trs_relative_terminates A R S`. `trs_relative_bound_NO` specializes NO.
The concrete module correctness obligations are discharged by integrated soundness.
The category property and existing conditional equivalences are unchanged.

`trs_relative_serialized_decision` uses `certify_proof_integrated False None None None
text` with the production-parser premise for the same exact input, property and
decision, and the runtime guard. This premise remains explicit: there is no formal
proof that the external Rust/Python comparisons imply the Isabelle parser result.
No new axiom, admission, certificate format or generated checker logic is introduced.

## Parsing, dispatch and original-input enforcement

```sh
ferrum cert check-relative original.ari proof.xml --answer no --ceta ../CeTA/ceta
```

Use `--answer yes` for termination. The native gate checks ARI declarations,
identifiers, arities and costs, compares strict and weak rule multisets separately
modulo per-rule variable renaming and injective quoted-symbol spelling aliases,
and requires full rewriting, the termination property and the requested decision.
No strategy or custom Q restriction is accepted. An omitted empty weak partition
is equivalent to an explicit empty partition. Variable left sides and extra
right-side variables are valid input; the extension branch of NO acceptance examines
weak-rule variables, while direct ranked loops need no variable restriction. Empty rule collections are supported.

TRS Relative now shares the strict ranked declaration validator with Standard
and Innermost. Cost classification accepts arbitrary natural numerals without
machine-integer truncation; positive costs also trigger relative dispatch even
when no weak rule occurs. Native TPDB certification validates category before
other dispatch and uses the bound gate. Explicit `--rewrite-strategy full` agrees
with Relative; innermost/outermost choices are rejected. Category directory
conflicts and unsupported declarations are rejected rather than ignored.

The independent replay audit uses both the extension guard and finite ranked-loop
checks with its own parser, before invoking CeTA or crediting a result. It retains
`relative-input-binding.json`. Both paths bind source, CPF and unified-checker
hashes and reject observed changes during checking. Direct CeTA and `cert check`
remain certificate-only checks and do not establish ranked original-input binding.
Ordinary ARI and plain CPF root terms are supported; legacy text-TRS and indexed
or marked roots are outside this gate.

## Original review verification and remaining trust

Build with `make isabelle-trs-relative-integrated ISABELLE=/path/to/isabelle
AFP="$AFP"`. The normal `Category_Relative_Integrated` build passed in 48 seconds
(67 seconds overall), including inherited-admission checks. Focused checks pass:
5 shared Rust binding tests, 12 ARI parser tests, the native category-dispatch
regression, 20 independent correspondence tests, 11 replay-harness tests and
13 Relative CLI cases, including a mixed strict/weak cycle and rejection after
removing its weak-step marker.
Standard and Innermost CLI regression gates also pass (6 and 11 cases).

The [receipt](data/trs-relative-integrated-verification-20261108.json) records actual
build/test outcomes, source snapshots and executable identities. The focused CLI
gate retains both the directly certified unrestricted counterexample and the
bound rejection, plus acceptance after adding a declared binary symbol. It also
covers empty and weak-loop YES, strict-loop NO, positive costs, partition changes,
strategy changes, wrong originals, wrong answers and mismatched proofs.

The broad Relative test filter is not an all-green release gate: the initial run
had four failures outside the changed boundary (LP-dependent discovery and an
installed-checker rejection of `rfcMatchboxAbsoluteBounds`). An experiment with
Isabelle's old bundled Z3 produced additional solver-sensitive failures. These
logs are retained; neither missing dependencies nor certificate incompatibility
is treated as a successful check. Focused boundary checks have separate results.
No solver, search processor, generated checking logic or installed CeTA binary
was changed to work around these failures.

The remaining trust boundary is as for [Standard](trs-standard-trust-boundary.md):
human interpretation of TPDB and ranked signatures, unverified ARI/XML parsing
and correspondence/guard implementation, artifact provenance and generated-code
execution, compiler/runtime and filesystem/process environment, and Isabelle/HOL
foundations including inherited oracle mechanisms. The guard is checked, not
left as a caller promise; this is still not a formally verified end-to-end parser.
The exact inherited oracle audit is recorded in the receipt.

CeTA proof sources changed in `CeTA/main`; installed production binaries did not.
A development Ferrum build exercises the revised paths. No full-frontier replay,
production promotion, checker completeness, or full ranked NO coverage is claimed.

## 2026-11-08 coverage follow-up

[Verification receipt](data/coverage-closure-20261108.json) records both successful
Isabelle session builds and the final strict replay: **Relative 113/113**
(97 YES, 16 NO) and **CSR 110/110** (105 YES, five NO). Original-input audits,
repeated unchanged-unified-CeTA checks and complete guidance authorization pass.
No root is lost. The final binary passes five Rust binding tests, 36 independent
Python audit tests and 77 native CLI cases, including unused declarations across
all six CSR YES proof families present in the retained corpus. The 77 cases
include 25 Outermost regressions for the shared witness scanner.

CeTA formal commits are `437e04f` (CSR) and `e3146a7` (Relative); Ferrum runtime
commit is `b91d7aec`. The final O2 Ferrum hash is
`1fdc35718db4996d75c2ddda022e3fda3efd10883398db4d2ad3d9b7d80dcd37`.
The unified CeTA remains
`5d50333bdfdccb3c143cc499162311a5846eb44ebdbfe46d493fec35c2b42d85`;
the unchanged Equational-reviewed oracle remains
`42ccbba8daea6a3cc152c7a76cd5bfcd08c1193de8df5493376037cf608591e9`.
Artifacts are in Ferrum `target/coverage-closure-reviewed-2`; the first passing
replay and intermediate failed proof/test attempts are preserved. Baseline
solver settings, category workers and root/atom ceilings are retained.

CSR has no remaining unused-declaration guard. Relative direct ranked loops
need no extension condition; other unrestricted NO families still do, because
unconditional transfer is false. No unchecked semantic or module premise is
introduced. Native parsing/witness comparison, inherited Isabelle mechanisms,
code generation, compilers, runtime and artifact provenance remain trusted.
This is a focused retention gate, not checker completeness, production promotion
or the independent two-checker release.
