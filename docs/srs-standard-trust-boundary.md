---
type: Formal Specification
title: "SRS Standard: concrete checker and original-input boundary"
status: stable
---
# SRS Standard review

The [published TermCOMP category](https://termination-portal.org/wiki/SRS_Standard)
asks whether every string-rewrite sequence stops. Its input representation is a
finite TRS of unary chains, with the same variable at both ends of each rule.
Different rules may use different variables. The [ARI TRS syntax](https://project-coco.uibk.ac.at/ARI/trs.php)
provides declarations and rules; unrestricted termination is the externally
selected category, not a strategy inferred from the spelling of a filename.
TPDB category directories are checked for conflicts with that selection.

## Reading order and semantics

Read [SRS_Spec_Base](../thys/Category_Specifications/SRS_Spec_Base.thy),
[SRS_Standard_Spec](../thys/Category_Specifications/SRS_Standard_Spec.thy),
[SRS_Equivalence](../thys/Category_Bridges/Bridge/SRS_Equivalence.thy),
[SRS_Unary_Encoding](../thys/Category_Bridges/Bridge/SRS_Unary_Encoding.thy),
then [SRS_Standard_Integrated](../thys/Category_Bridges/SRS_Integrated/SRS_Standard_Integrated.thy).
The human-facing property excludes infinite sequences of contiguous word
replacement, retaining the prefix and suffix. Empty words and empty left sides
are allowed. In particular, the empty-word self-loop is nonterminating.
There is no ground-term interpretation or requirement for a constant symbol.

`represents_words T R` requires that every term rule in `T` encodes a word rule
in `R` using a shared tail variable, and every word rule has such a representative.
It allows different tails between rules, duplicate list entries and any ordering.
`represented_words_iff` states precisely:

```
represents_words T R ⟹
srs_standard_terminates R ⟷ SN (Trs.rstep T)
```

This is unrestricted term rewriting. There is no additional signature-extension
or proof-family guard for either answer. The finite certificate rule list
supplies finite input; the equivalence itself holds without a finiteness premise.

## Concrete checker statements

`srs_standard_integrated_decision` assumes the representation correspondence and
actual acceptance of
`certify_integrated_cert_problem False (Inn_TRS_input No_Strategy Rs [])
Termination (Decision b) certificate`, and concludes
`b ⟷ srs_standard_terminates R`.
The YES and NO corollaries specialize `b`. Concrete module correctness follows
from the integrated checker theorem, rather than remaining a module contract.
Assumption checking is disabled; the input has no weak rules, Q restrictions,
normal-form substitution restriction or restricted rewrite strategy.

`srs_standard_serialized_decision` composes the actual integrated parser and
assumption-free serialized checker with that conclusion. Its parser-result
premise identifies the exact parsed input, property, answer and certificate.
It does not claim a formally verified ARI parser or ARI-to-CPF comparator.

## Enforced runtime boundary

Ferrum exposes `cert check-srs-standard ORIGINAL.ari PROOF.xml --answer yes|no
--ceta CETA`. It checks the complete ARI declaration grammar, unary declarations
including unused ones, shared tails and exact rule multisets modulo per-rule
variable renaming. It rejects weak rules and restricted CPF strategies. The
property and decision must agree. Existing immutable source/CPF/checker checks
and the exact successful checker marker remain required.

Native TPDB certification and the independent Python replay audit enforce the
same category constraints. The independent parser does not call Ferrum's parser
or canonicalizer. The bound command accepts the published unary `(format TRS)`
representation; the separate native `(format SRS)` relative-word extension is
not silently treated as this interface's syntax.

## Trust and verification

The runtime parsers, correspondence comparison, artifact handling, generated
code execution, compilers and Isabelle/HOL infrastructure remain trusted.
An admission audit and inherited-oracle audit accompany the formal build.
No generated checker logic, certificate format or installed production binary
is changed. Checker soundness does not imply completeness.

The normal integrated session and admission audit pass. The inherited oracle
names are `Regexp_Method.check_eqv` and `Types_To_Sets.cancel_type_definition`;
this is not a kernel-only proof claim. Human approval is not recorded.

## Large-certificate audit handling

SRS replay exposed full-certificate buffers and serial Python XML work in the
threaded harness. Certificate hashes, metadata extraction, diagnostic tag scans
and artifact copies now stream; root workers and independent audits use isolated
processes at the same 32-root category concurrency. Input/CPF/checker identities
are still checked before and after certification, and malformed trailing XML is
still rejected. Earlier interrupted runs are preserved as nonfinal evidence.

## Recorded verification

[Verification receipt](data/srs-standard-review-20261108.json) records the exact
source and executable identities. All **1,720/1,720 SRS Standard** protected
root/polarity pairs pass, and all **3,610/3,610** across the five reviewed
categories are retained. Source binding, repeated unchanged-CeTA checks and
complete guidance-receipt audits pass. There are no unresolved replay roots.

Nineteen Rust parser/export tests, 35 independent Python audit tests, 14 harness
tests and 65 bound CLI cases pass. Three native fixtures export and certify:
word deletion with an unused unary declaration, an empty-word self-loop and
rules with different tail variables. All 1,720 inputs pass both parser preflights.

The development oracle is unchanged from the CSR review, SHA-256
`1610d2312ef7c7e8ef694e36a1e0181ccd423b7e4989e92b3d071c4c7cbfa12c`. No re-keying or new advice was needed.
Ferrum SHA-256: `a6fd6acbb014412299190f6ea4c9af4ff3f3fde86e3e8d6aed69cb7798aaac36`.
Unified CeTA SHA-256: `5d50333bdfdccb3c143cc499162311a5846eb44ebdbfe46d493fec35c2b42d85`.
