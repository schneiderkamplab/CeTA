---
type: Formal Specification
title: "SRS Standard, Relative and Cycle specifications"
status: draft
---
# String-rewriting specifications

Read [SRS_Spec_Base](../thys/Category_Specifications/Spec/SRS_Spec_Base.thy)
for finite words and contiguous replacement, then the category definitions:
[Standard](../thys/Category_Specifications/Spec/SRS_Standard_Spec.thy),
[Relative](../thys/Category_Specifications/Spec/SRS_Relative_Spec.thy), and
[Cycle](../thys/Category_Specifications/Spec/SRS_Cycle_Spec.thy).
Each property excludes infinite sequences of its explicitly defined steps.
`string_problem R` requires finite rules. Empty words and empty left sides
are allowed. There are no term variables in these word-level specifications.

A relative block contains one strict replacement between finite weak sequences.
A cycle step rotates a word, makes one replacement, and may rotate the result.
Rotation by itself does not count as progress. The
[examples](../thys/Category_Specifications/Spec/SRS_Examples.thy) cover empty
systems, word deletion, internal replacement, self-loops, harmless weak loops,
and an actual replacement that becomes a cycle self-loop after rotation.

## Equivalences

[SRS_Equivalence](../thys/Category_Specifications/Bridge/SRS_Equivalence.thy)
proves `string_step_iff` and `relative_string_step_iff`, followed by
`srs_standard_terminates_iff` and `srs_relative_terminates_iff`. Their conclusions
are equivalence to `SN (srs_step R)` and `SN_rel (srs_step R) (srs_step S)`.
The word and rule translations are identities because both use HOL lists.
The corresponding nontermination theorems negate these equivalences.

[SRS_Unary_Encoding](../thys/Category_Specifications/Bridge/SRS_Unary_Encoding.thy)
defines `word_rules x R`: each word becomes a chain of unary function symbols
ending in the same variable `x` on both rule sides. It proves preservation of
word steps, reflection by projection on unary terms, and:

- `srs_standard_unary_iff`: the canonical Standard property iff
  `SN (rstep (word_rules x R))`.
- `srs_relative_unary_iff`: the canonical Relative property iff
  `SN_rel (rstep (word_rules x R)) (rstep (word_rules x S))`.

These have no additional hypotheses. Encoded weak rules preserve their one
variable, so the relative signature-extension condition is proved internally.

[SRS_Cycle_Equivalence](../thys/Category_Specifications/Bridge/SRS_Cycle_Equivalence.thy)
proves `cycle_string_step_iff` and `srs_cycle_terminates_iff`, identifying the
canonical cycle property with `SN (cycle_step R)` without extra hypotheses.

## Checker connections

[SRS_Checker_Bridge](../thys/Category_Specifications/Bridge/SRS_Checker_Bridge.thy)
provides YES and NO corollaries for Standard and Relative. Each assumes finite
input rules, `tp_spec I`, `dpp_spec J`, `nfs = False`, empty Q, and strict rules
exactly `word_rules x R`. Standard requires empty weak rules; Relative requires
weak rules exactly `word_rules x S`. All certificate calls use `False` to forbid
assumptions. Standard NO uses `check_trs_nontermination_proof`; Relative NO uses
`check_reltrs_nontermination_proof`. Both YES results use
`check_trs_termination_proof`.

The [cycle bridge](../thys/Category_Specifications/Bridge/SRS_Cycle_Checker_Bridge.thy)
connects `check_cycle_transport`, `check_cycle_embedding` and
`check_cycle_morphism_direction` to `not srs_cycle_terminates (set R)`.
These existing Boolean checks have no assumption mechanism. This cycle module
exposes NO checks only; no YES checker API or YES soundness corollary is claimed.

The normal package build passed with these additions on 2026-11-07, including
all inherited-admission audits. Specifications took 2 seconds, the bridge
session 37 seconds and the additional Cycle_Checker dependency 6 seconds;
overall time was 54 seconds. Log: `target/trs-innermost/package-relative-strings-2.log`.
The [package page](category-specifications.md) explains the common structure
and the boundary of these semantic claims.

The [Standard concrete review](srs-standard-trust-boundary.md) now instantiates
the integrated and serialized checker for per-rule tail variables and enforces
original-input binding. Its verified replay and trust boundary supersede the
parameterized Standard bridge status above; Relative and Cycle remain separate.
