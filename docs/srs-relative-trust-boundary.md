---
type: Formal Specification
title: "SRS Relative: concrete checker and original-input boundary"
status: stable
---
# SRS Relative review

The [published category](https://termination-portal.org/wiki/SRS_Relative)
asks whether every reduction uses strict rules only finitely often. Weak-only
infinite rewriting is permitted. Both components are finite string systems,
represented by unary term rules with a shared tail variable on both sides.
Different rules may use different tail variables.

Read [SRS_Spec_Base](../thys/Category_Specifications/Spec/SRS_Spec_Base.thy),
[SRS_Relative_Spec](../thys/Category_Specifications/Spec/SRS_Relative_Spec.thy),
[SRS_Unary_Encoding](../thys/Category_Specifications/Bridge/SRS_Unary_Encoding.thy),
then [SRS_Relative_Integrated](../thys/Category_Specifications/SRS_Integrated/SRS_Relative_Integrated.thy).
The canonical property excludes infinite sequences of blocks containing one
strict replacement and finite weak prefixes/suffixes. This agrees with the
published infinitely-many-strict-steps criterion. Empty words, empty left sides,
empty partitions and weak self-loops are allowed; there is no groundness premise.

## Concrete statements

`represented_word_steps` identifies the entire unrestricted term rewrite relation
of an encoded word system with that of its common-tail encoding. Both directions
allow different variables between rules. `represented_relative_words_iff` applies
this independently to the strict and weak partitions and concludes:

```
represents_words T R ⟹ represents_words U S ⟹
srs_relative_terminates R S ⟷ SN_rel (Trs.rstep T) (Trs.rstep U)
```

`srs_relative_integrated_decision` combines this with actual acceptance of
`certify_integrated_cert_problem False (Inn_TRS_input No_Strategy Rs Ss)
Termination (Decision b) certificate` and concludes
`b ⟷ srs_relative_terminates R S`. YES and NO specialize this decision theorem.
`srs_relative_serialized_decision` uses the actual integrated parser result and
assumption-free serialized checking, with no property or answer overrides.

There is no extra signature or proof-family guard for either answer. The general
TRS Relative NO obstacle does not apply: shared string tails imply the needed
weak-rule variable preservation. The representation premises identify the source
problem; they are enforced by the runtime binding and are not unproved checker
module contracts.

## Input boundary and trust

`ferrum cert check-srs-relative ORIGINAL.ari PROOF.xml --answer yes|no --ceta CETA`
checks the unary `(format TRS)` representation, including unused declarations
and the tails of both rule partitions. Missing costs denote strict rules; zero
costs denote weak rules. Positive integer costs have the same termination
meaning as cost one. Negative or malformed costs are rejected. The separate
native `(format SRS)` word extension is not accepted by this bound interface.

Original and CPF strict/weak multisets must match modulo per-rule variable
renaming. Restricted strategies, changed partitions, property or answer are
rejected. Native TPDB certification and independent replay enforce the same
boundary, retaining immutable source, certificate and unified-checker identities.

Parsing, correspondence comparison, artifact handling, compilers, execution and
Isabelle/HOL infrastructure remain trusted. Normal builds and oracle/admission
audits must pass before completion is recorded. No generated checker logic,
certificate format or installed production executable is changed. These results
concern soundness, not checker completeness. Human approval is not recorded.

Verification and protected replay pass. The inherited oracles are
`Regexp_Method.check_eqv` and `Types_To_Sets.cancel_type_definition`; this is not
a kernel-only proof claim.

## Recorded verification

[Verification receipt](data/srs-relative-review-20261108.json) pins sources,
executables, theorem audits and replay evidence. Normal Isabelle builds pass
without admissions or new axioms. All **403/403 SRS Relative** protected cases
(363 YES, 40 NO) and all **4,013/4,013 across six reviewed categories** are
retained. Source audits, repeated unified-CeTA checks and complete guidance
receipt audits pass; no replay root is unresolved.

Twenty-one Rust tests, 36 Python audit tests, 15 harness tests and 82 bound CLI
cases pass. Four native fixtures cover weak-only loops, empty-word weak loops,
a mixed strict/weak cycle and an empty weak partition; each exports and certifies.
All 403 inputs pass both parser preflights. Explicit SRS Relative metadata now
selects relative dispatch even without rule costs. The protected empty-weak
case still certifies with existing guidance; no re-keying was needed.

Ferrum SHA-256: `df989cd8ffa93fa73abc22b2ee7d7d455420622f400e8be5b4f6c156ae15f11f`.
Unchanged unified CeTA SHA-256: `5d50333bdfdccb3c143cc499162311a5846eb44ebdbfe46d493fec35c2b42d85`.
Unchanged development oracle SHA-256: `1610d2312ef7c7e8ef694e36a1e0181ccd423b7e4989e92b3d071c4c7cbfa12c`.
No production promotion or independent two-checker release is claimed.
