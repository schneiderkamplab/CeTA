---
type: Formal Specification
title: "Rewriting category specification package"
status: draft
---
# Rewriting category specifications

The package lives in [Category_Specifications](../thys/Category_Specifications/ROOTS).
Isabelle theories are its modules; sessions are its build units. The lightweight
`Category_Specifications` session depends on HOL. The separate
`Category_Specification_Bridges` session depends on the existing proof checker.
Definitions never import their equivalence proofs or checker connections.

Read [TRS_Spec_Base](../thys/Category_Specifications/Spec/TRS_Spec_Base.thy)
first for finite terms, ranked signatures, substitutions, contexts and ordinary
steps. Then read each category definition, its examples, equivalence theory and
checker bridge, in that order. Shared mathematical vocabulary belongs in the
specification layer; shared IsaFoR translations belong in the bridge layer.

- [Assumptions and category-by-category review](category-assumptions-review.md).
- [TRS Standard](trs-standard-specification.md).
- [TRS Innermost](trs-innermost-specification.md).
- [TRS Relative](trs-relative-specification.md).
- [SRS Standard, Relative and Cycle](srs-specifications.md).

The authorized extension scope also includes TRS Relative, Outermost,
Context-sensitive, Conditional and Equational; SRS Standard, Relative and Cycle;
and Higher-order Rewriting. Relative, Context-sensitive and the three SRS correspondences are implemented
with the coverage limits recorded in the review register. [Higher-order](higher-order-trust-boundary.md) now has a compiled typed equivalence
and sixteen concrete YES and four NO checker corollaries. [Outermost](trs-outermost-trust-boundary.md) has ranked equivalence and concrete/serialized YES and direct-loop NO connections. [Conditional](trs-conditional-specifications.md) has separate ordinary and operational specifications over a common inference layer, exact ranked equivalences, concrete YES/NO bridges and a strict 239/239 focused replay. [Equational](trs-equational-specification.md) has shared-term ranked semantics, exact ranked equivalence, concrete/serialized YES and ordinary-proof NO bridges, and a strict 71/71 focused replay.
Probabilistic, integer and complexity categories are outside this milestone.

## Verification

```sh
make isabelle-category-specifications ISABELLE=/path/to/isabelle
make isabelle-category-specification-bridges ISABELLE=/path/to/isabelle AFP="$AFP"
python3 scripts/check_okf.py docs
```

The old Standard make targets remain aliases. The original Standard build
receipt is retained as historical evidence. The Standard and Innermost package build passed on 2026-11-07: 2 seconds
for specifications, 23 seconds for bridges, 39 seconds overall. Both checker
bridges passed their inherited-admission audits. The
[verification receipt](data/category-specifications-standard-innermost-20261107.json)
records the checked source hashes and log. Later category additions are
verified separately.

Reviewing these definitions and checking their correspondence proofs establishes
what an accepted certificate means. It does not establish checker completeness,
parser correctness or correspondence to a particular compiled executable.
No certificate format, generated checking code or production binary is changed.

The Relative and SRS additions passed their normal package build and
admission audits. Their [verification receipt](data/category-specifications-relative-strings-20261107.json)
records a retained source snapshot and the successful build log.

The optional `Category_Standard_Integrated` session connects the canonical
Standard property to the concrete integrated checker. It is separate from the
lightweight specification and ordinary bridges; see the
[trust-boundary review](trs-standard-trust-boundary.md) for its verification
status and explicit serialized-input premise.

The optional `Category_Innermost_Integrated` session provides the same concrete
and serialized connection for strict Innermost (`nfs=false`); see its
[review and trust boundary](trs-innermost-trust-boundary.md).

`Category_Relative_Integrated` adds concrete YES and guarded NO soundness for
the ranked Relative specification. See the [review](trs-relative-trust-boundary.md)
for the necessary signature distinction and incomplete NO coverage.

A subsequent [strict replay of the three reviewed categories](../../ferrum/docs/reviewed-categories-replay-20261108.md)
completed on the protected 1,780-root baseline: 1,316 certified, 464 Unknown.
All accepted proofs pass the follow-up audits. Innermost state-key changes
explain 452 losses across Standard/Innermost; 12 Relative losses remain for
separate diagnosis. This is not a production promotion or full-frontier replay.

## Reviewed-category replay repair

The [updated oracle and replay](../../ferrum/docs/reviewed-oracle-repair-20261108.md)
now retains all 1,780 reviewed Standard, Innermost and Relative roots with source
binding and repeated checks by one rebuilt unified CeTA executable. Main's
verified export already supported the parser field rejected by the old installed
binary; no formal or generated checking logic changed for this repair.
[Checker identity and validation](data/reviewed-oracle-repair-20261108.json).
The installed executable and full fifteen-category release remain separate.

The [Context-sensitive concrete review](trs-context-sensitive-trust-boundary.md)
adds session `Category_Context_Sensitive_Integrated`, complete declared-map
binding, and explicit checked YES coverage for signatures larger than the rules.

The Higher-order sessions build with `make isabelle-higher-order-integrated`.
See the [review](higher-order-trust-boundary.md) for exact semantics and the
original-input binding boundary.

The Outermost sessions build with `make isabelle-outermost-integrated`. See the
[Outermost review](trs-outermost-trust-boundary.md) for exact witness guards and proof coverage.
