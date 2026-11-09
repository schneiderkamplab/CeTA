---
type: Formal Specification
title: "TRS Standard: integrated checking and remaining trust boundary"
status: draft
---
# TRS Standard: integrated checking and remaining trust boundary

This page supersedes the outstanding-obligation list in the initial
[Standard input review](trs-standard-input-review.md). The integrated session and focused runtime gates passed on 2026-11-08;
verification details are recorded below.

## Formal connection

[TRS_Standard_Integrated](../thys/Category_Bridges/Integrated/TRS_Standard_Integrated.thy)
composes `certify_integrated_cert_problem_sound` with the canonical ranked
Standard equivalence. The concrete integrated checker supplies its module
correctness proofs. The resulting decision theorem has these premises:

- `trs_problem A R`: finite, signature-correct rules and infinitely many variables;
- the parsed rule list represents exactly `to_rules R`;
- the integrated checker, with assumptions disabled, returns `Certified` for
  `Inn_TRS_input No_Strategy Rs []`, `Termination`, and `Decision b`.

The conclusion is `b` iff `trs_standard_terminates A R`. Separate YES and NO
corollaries specialize it. There is no user-supplied processor-correctness
hypothesis and no additional variable-rule restriction.

[TRS_Standard_Serialized](../thys/Category_Bridges/Integrated/TRS_Standard_Serialized.thy)
adds the actual serialized entry point `certify_proof_integrated`, with no
external input/property/answer overrides. Its explicit parser premise states
that the production parser produces that exact Standard problem and answer.
It does not assume an arbitrary certificate describes the original benchmark.

The separate `Category_Standard_Integrated` session leaves the independent
specification and its lightweight session unchanged. Build with
`make isabelle-trs-standard-integrated ISABELLE=/path/to/isabelle AFP="$AFP"`.

## Runtime original-input enforcement

Ferrum's new command is:

```sh
ferrum cert check-standard original.ari certificate.xml --answer yes --ceta /path/to/ceta
```

Use `--answer no` for nontermination. This command checks the original ARI
syntax and declarations, rejects incompatible TPDB category paths, and compares
its rules with the CPF root. It requires unrestricted Standard rewriting,
no weak rules, the termination property and the requested answer. Only per-rule
variable renaming and injective quoted-symbol spelling aliases are permitted.
The checker receives the same compared CPF bytes with assumptions disabled.
This gate supports ordinary ARI and plain CPF root rules/terms. Legacy text-TRS
input and indexed/marked CPF roots are rejected rather than certified without
correspondence; this is a coverage limit, not an extra mathematical hypothesis.

The command returns a JSON receipt only after both correspondence and CeTA
succeed. It records original-input, CPF and checker SHA-256 hashes. The compared
CPF is written to an exclusively created private temporary file. Input,
certificate and checker changes observed across verification cause rejection.
These checks assume an ordinary trusted local filesystem/process environment;
they are not protection against an adversarial operating system.

The native TPDB certification command validates the Standard category before
other dispatch and uses this gate for Standard before
counting a result as certified. The
[TermCOMP replay harness](../../ferrum/scripts/termcomp_trs_compare.py) now runs
its independent Python correspondence audit before granting Standard
certification credit, retains a binding receipt, and rejects changes across
checking. The existing release-wide post-audit remains in place.

The older certificate-only `cert check` command and direct `ceta certificate.xml`
remain certificate-input checks. They do not claim original-benchmark
correspondence and must not be used alone to justify a Standard benchmark result.
This change does not retrofit every arbitrary historical or third-party caller.
The updated production source paths have been tested in a development Ferrum
binary; installing/promoting a production release is not part of this milestone.

## Obligation disposition

| Obligation | Disposition |
| --- | --- |
| Canonical property versus ordinary rewriting | Proved in Isabelle, in both directions. |
| Concrete integrated checker module contracts | Discharged by the existing integrated theorem and the new composition. |
| Exact Standard configuration for accepted calls | Explicit in the theorem; enforced by the bound runtime callers. |
| Original rules, category and answer versus CPF | Enforced and mutation-tested in the updated native and replay callers. |
| Parser/comparator correctness | Remains trusted software; not an Isabelle proof. |
| Production binary promotion and complete replay | Not performed in this milestone. |

## Remaining trust boundary

1. **Mathematical specification and external category conventions.** Human
   review must establish that the independent definition captures TPDB Standard.
   The published definition and our review agree; no machine proof connects a
   natural-language category page to the HOL definition.
2. **Parsing and correspondence software.** ARI tokenization, declaration
   validation, CPF/XML parsing, category metadata, variable/symbol normalization,
   and the Rust/Python comparison code are tested but not verified in Isabelle.
   In particular, the runtime comparison has not been formally proved to imply
   the serialized theorem's parser premise. Sharing an ARI parser between the
   native prover and native gate is a common implementation dependency; the
   replay audit uses an independent parser.
3. **Artifact identity and execution.** The receipt identifies the tested
   executable. Hashing does not prove it was compiled from these exact verified
   sources. Code generation, handwritten Haskell adapters, compiler/runtime,
   libraries and the local execution environment remain trusted. This milestone
   does not rebuild or replace the installed CeTA binary or assert a new
   source-to-executable provenance proof.
4. **Isabelle/HOL foundations.** The HOL logic, kernel and trusted infrastructure
   remain foundational. Admission audits rule out skipped proofs; they do not
   remove all inherited trusted mechanisms or prove the kernel correct.
   The serialized theorem's dependency audit reports the inherited oracles
   `Regexp_Method.check_eqv` and `Types_To_Sets.cancel_type_definition`.
   They are part of the trust boundary; this is not a kernel-only proof claim.
5. **Correct invocation.** The original file, intended category and expected
   answer must be supplied through a bound-verification path. A direct check of
   a different, internally valid certificate still proves something about that
   certificate's input, not the intended benchmark.

These are explicit remaining dependencies. The theorem and tested runtime gate
do not establish checker completeness, a verified parser, or a full-frontier
release result. No new axiom, certificate format, generated checking logic or
installed checker binary is introduced by this work.

## Verification record

The normal `Category_Standard_Integrated` build passed with both theories,
including their inherited-admission checks: 51 seconds for the session,
70 seconds overall with warmed dependencies. The initial build also checked
the required integrated-checker dependency sessions successfully. A separate
Isabelle process checked the serialized theorem and recorded its inherited
oracle names. No admissions or new axioms were added.

Runtime validation passed 15 Rust tests selected by `standard_`, 18 independent
correspondence tests, 8 replay-harness tests, and 6 CLI gate cases. The CLI cases
retain their actual source/CPF fixtures and receipts. Both repositories' OKF
documentation checks pass. Existing unrelated Rust warnings remain.

The [verification receipt](data/trs-standard-integrated-verification-20261108.json)
records reviewed source hashes, retained source snapshots, test/build logs,
repository heads and executable hashes. The snapshot is scoped to this review;
it is not a full release provenance record. The installed CeTA hash is unchanged
from the earlier input-path review. No installed production binary was promoted.
