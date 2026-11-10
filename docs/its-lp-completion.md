---
type: Implementation Plan
title: "ITS and LP semantic correspondence completion"
status: draft
---
# ITS and LP semantic correspondence completion

This milestone closes the proof and focused runtime obligations in the
[category review](its-lp-specifications.md) and the
[Ferrum boundary review](../../ferrum/docs/its-lp-category-boundary.md).
This ledger records requirements, not assumed results. Kernel, extraction and
compiler/runtime trust must be stated precisely; their existence is not an
unfinished proof obligation. Prolog and LeTA remain outside this task.

## Completion ledger

| Requirement | Evidence required | Current state |
| --- | --- | --- |
| Standalone ITS and distinct finite/rational/infinite LP and cut specs | HOL-only build, definition-only package guard, reference review | Checked: 28 HOL-only definition theories; standalone build and package guard pass |
| ITS YES/NO semantic correspondence | Actual checker corollaries and no-admission audit | Checked YES/NO bridge; no-admission audit; final session gate passes |
| ITS original-input boundary | Entry declaration, type/sort handling and arity conventions; positive and mutation tests | Reviewed: duplicate/forward entry declarations and zero-argument rules rejected; Boolean sorts explicitly unsupported; 18 frontend tests pass |
| Cut table YES, three domains | Actual table acceptance to each canonical predicate | Verified in domain-bridge receipt |
| Cut source NO, three domains | Actual source-NO acceptance to canonical infinite execution | Verified, oracle-free, including barrier-growing loop example |
| Cut constructor YES, three domains | Concrete constructor residual checker and shared domain root-table proof | Checked in `Category_LP_Cut_Family_Bridges` |
| Cut MGU YES, three domains | Domain-specific most-general source, free-variable knowledge, table and concrete residual checker | Checked: full table, constructor residual, canonical simulation and all three serialized corollaries |
| Cut return and module YES, including triples | Four concrete endpoints, each interpreted in all three domains | Checked in `Category_LP_Cut_Return_Bridge` |
| Cut composed/nested YES, including triples | Each actual acceptance family to its declared canonical domain | Checked in `Category_LP_Cut_Composition_Bridge` and `Category_LP_Cut_Nested_Bridge` |
| Cut segment/free/projected/triple YES | Each actual acceptance family to its declared canonical domain | All four checked, with combined audit of all 51 cut checker corollaries |
| Cut projected YES | Exact certificate source/modes and concrete projected acceptance to canonical predicate | Checked in `Category_LP_Cut_Projected_Bridge`; source binding verified below |
| Pure-LP NO, every dispatch family | Actual finite witness/loop to most-general execution; exact modes and source binding | All seven endpoints checked, including pattern acceleration; combined audit has no oracle dependencies |
| Pure-LP YES dispatch coverage | Inventory all executable acceptance branches and connect their respective domains | Eleven concrete endpoint corollaries checked, including the finite-named artifact; source binding verified below |
| Semantic selection and identity | Finite competition default, explicit separate variants, complete state identity, rejection of mismatches | Verified: finite default, explicit rational/infinite choices, distinct identities, exact certificate subjects and cross-domain guidance rejection |
| Original input/certificate correspondence | Exact program, clause order where relevant, query modes and semantic domain; negative mutations | Verified: 18 pure and 17 cut envelopes; source/query mutations rejected; complete subjects retain domains |
| Integration verification | Relevant sessions, theorem audits, focused runtime tests, documentation checks and immutable evidence | Passed: combined Isabelle gate, 365 LP tests, CLI selection test, 12 certified domain runs / 24 CeTA checks; documentation checks pass |

No accepting family is to be silently dropped to make the review pass, and no
unsupported semantic implication is to become a caller-supplied assumption.
The production checker binary and generated checking logic are preserved.
Any required source change must follow the binding architecture and regeneration
contracts; no full-frontier replay or parser-correctness theorem is implied by a
focused test gate.

## Existing evidence

The [domain-bridge receipt](data/lp-cut-domain-bridges-20261110.json) pins the
completed table-YES/source-NO milestone. It does not establish completion of the
other rows. Source hashes and successful logs must be refreshed for newly
verified results without rewriting historical receipts.

The [family-bridge receipt](data/its-lp-family-bridges-20261110.json) records the
constructor and ten additional pure-LP YES corollaries, together with the
checked domain-specific MGU foundations. Later receipts close the MGU, return and remaining family obligations.

The [MGU bridge receipt](data/lp-cut-mgu-bridges-20261110.json) records the
completed MGU endpoint in all three domains. The [return-family receipt](data/lp-cut-return-bridges-20261110.json) records
return and module constructor/triple endpoints. The [composition receipt](data/lp-cut-composition-bridges-20261110.json) closes composed and nested constructor/triple endpoints. The [projected receipt](data/lp-cut-projected-bridge-20261110.json) closes the projected return checker. All cut acceptance families are now covered by the combined audit below.

The [segment receipt](data/lp-cut-segment-bridge-20261110.json) records basic segment acceptance in all three domains. Its split proof derives domain membership of full returned environments from actual execution. The later combined receipt below closes the other segment endpoints.

The [complete cut-family receipt](data/lp-cut-all-checkers-20261110.json) records 17 dispatcher endpoints, each with three separate canonical corollaries, and the combined no-admission/oracle audit. This closes the cut proof-family coverage obligation. The final receipt below also closes runtime semantic selection and binding.

The [first pure-LP NO receipt](data/lp-no-basic-bridges-20261110.json) records four actual endpoints, each covering all three canonical domains without oracle dependencies. It includes finite witness proofs and the shared universal-MGU lifting theorem. The later [complete NO receipt](data/lp-no-all-bridges-20261110.json) closes recurrent-pair, pattern (including acceleration) and affine endpoints.

## Completion evidence and limits

The [completion receipt](data/its-lp-completion-20261110.json) pins the final source
hashes, build logs, theorem audits and focused runtime gate. Earlier receipts are
immutable historical milestones. The gate uses one unchanged unified CeTA binary.
It is not a full frontier replay, a completeness claim, a release promotion, or a
proof of source-parser/compiler correctness. The receipt records the verified pre-commit working-tree snapshot; its historical
commit and working-tree fields are preserved when the sources are committed.

No semantic equivalence, MGU existence, domain closure or processor soundness
obligation remains as a caller-supplied assumption. Actual parsing and acceptance
premises identify the input and checker event. The remaining trust surface is
Isabelle/HOL and its kernel; inherited oracle mechanisms named in the YES audits;
code extraction, generated code and compiler/runtime; and source parsing,
translation and binding. ITS arithmetic interpretation is included in that review.
Pure-LP and cut NO corollaries have no oracle dependencies. Boolean ITS location
arguments remain explicitly unsupported. Prolog and LeTA are outside this milestone.
