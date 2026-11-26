---
type: Verification report
title: "CPF 6 CeTA support and validation"
status: stable
---
# CPF 6 support and validation

The milestone is complete. It migrates the existing unified LP, LP-with-cut and Prolog interfaces
to CPF 6 XML, preserving CPF 3–5. LeTA remains deferred. This is certificate
integration and coverage retention, not a claim of complete proof search or
support for every Prolog dialect feature.

The syntax inventory covers 71 exposed source/residual proof forms, including
15 newly integrated Prolog source forms. Schema generation resolves 123 parser
groups directly from the existing Isabelle parser syntax, without wildcard
proof payloads. The experimental context-reference formalization is not an
exported/dispatched checker interface and is explicitly excluded. Residual
constructors can be supported inside a source proof without being standalone
source theorems.

## Completed CPF 6 gates

All 1,274 previously certified mode entries pass CPF 6 schema validation,
original-source audits and two checks by one immutable unified CeTA. The 80
baseline unresolved mode entries have explicit dispositions. Decoder comparison
passes all 364 retained Prolog certificates: Haskell drops the program only for
the undefined-query mathematical interface, after validating its definition
list; Rust retains it for independent original-source auditing.

All four fresh replay phases retain every required success:

| Category | Strict YES / NO / unknown | Learned YES / NO / unknown |
| --- | --- | --- |
| LP, 363 inputs | 240 / 123 / 0 | 240 / 123 / 0 |
| LP with cut, 93 inputs | 84 / 9 / 0 | 83 / 8 / 2 |
| Prolog, 221 inputs | 90 / 97 / 34 | 80 / 97 / 44 |

There are 677 distinct inputs, evaluated in both modes: 1,354 mode entries,
1,274 certified and 80 unresolved. Final fresh-output auditing passes schema,
version, polarity, source binding and two additional CeTA checks for every
certified entry. The oracle and learned policies are unchanged. Original category
limits are preserved; replay concurrency is recorded and is not a matched
runtime comparison.

The regression suite passes 397 cases over 37 retained root constructors,
including wrong versions/polarity/property, extra/missing evidence, duplicate
inputs and unsupported Prolog profiles. The same corpus is bundled as compressed
fixtures. Eight focused contextual, composed, established, finite and guarded
gates pass; seven existing CPF 6 schema suites and the schema inheritance tests
pass. The LP translation gate passes 34 cases. Ferrum passes 29 codec tests and
783 LP tests (30 existing ignored tests). The end-user examples both certify.

A context-to-ITS diagnostic produced a schema-valid proof rejected by both the
CPF 5 checker on decoded native XML and the CPF 6 checker. It is retained as a
pre-existing search/certification limitation, not counted as a certified result
or a migration regression. The migration preserves the mathematical checker;
it does not accept the rejected proof to increase coverage.

## Checker identity and compatibility

CeTA changed in its handwritten CPF 6 input adapter, category integration and
schemas. No generated mathematical checking logic or export archive changed.
The selected tree is `../CeTA-cpf6-milestone`, based on main
`9248bad51ca8c74ed96702b9f249445bb7a0e807`. The unified O2 executable was built
with `make ceta`: `target/cpf6-milestone/pilot-unified/ceta`, SHA-256
`e436496317d720872048c88867e4e08cb21f7694e35231f27845361e08717f75`.

Ferrum's selected tree is `../ferrum-cpf6-milestone`, based on main
`c313c23fbcfa4e8afac4763d6204fa425deae953`. Release binary SHA-256:
`8468ec2c3e852d92b515348b6c4eb9a25364ba4c64be0be54c9180b0601f70c6`.
The frozen oracle SHA-256 remains
`49c7bfddf5daea0d0b4f07b2d0453e68a17727d2fd3d221255d30a0edeeaf81e`.

All 22 compatibility gates pass on this same checker: 596 CPF 3 compatibility
cases, the focused CPF 4 gates, all 4,821 retained CPF 4 certificates twice,
and all 2,674 retained CPF 5 mode certificates twice. The original 170 unresolved
first-order inputs remain historical no-proof results, not rejected certificates.

Full local artifacts are under `target/cpf6-milestone`. Use the
[CPF 6 user guide](../xml/CPF6.md) for end-user format and checking instructions.


The [machine-readable summary](data/cpf6-milestone-20261126/summary.json) and
[evidence archive](data/cpf6-milestone-20261126/evidence.zip) record the exact
commands, source/build hashes, outcomes and failed preliminary attempts. The
complete proof corpora and binary builds remain local. Production guidance and
the installed checker were not replaced. Work pauses at this milestone;
LeTA remains deferred.
