---
type: Historical Report
---
# Refactoring paths with incomplete genuine replay coverage

The user explicitly authorized this follow-up after the earlier consolidation
left these paths deferred. Work remains isolated on `consolidated`.

## Changes

Relative ADP production theories move from `dev/Relative_ADP_Dev` to
`thys/Relative_ADP`, preserving semantics/checker/integration layers. Old build
directories forward through `ROOTS`; existing session names are retained to avoid
breaking session-qualified imports. The reproducible build recipe uses the new
production paths.

Five general injective-renaming lemmas are extracted from the ADP certificate
adapter into `Dependency_Pair_Injective_Renaming`. Its only import is the existing
framework dependency-pair implementation. Compatibility theorem aliases retain
the adapter's qualified names. The nonminimal finite-DP theorem keeps its exact
Q, empty-component and injectivity assumptions.

The RZ adapter now calls `rz_generated_rules_sound`: an explicit criterion from
source well-formedness, quasi-left-linearity, grounding/marker freshness,
flat-map coverage, pattern validity, automaton coverage and termination of the
generated TRS. Recursive child certification is handled separately by the adapter.
The executable definitions, certificate forms, check order and failure messages
are unchanged. The flat-map check remains an explicit criterion premise even
though the underlying soundness derivation does not use it.

Six formal RZ guard-rejection lemmas and four ADP index-rejection lemmas supplement
the existing focused tests. They are not represented as real Ferrum replays.

## Evidence and limits

Verification passed for the immutable source tree
`3ba09e4ce707c5f590f2ee942a09fbc96f5f3ae1`. All four production Isabelle targets
and the explicit RZ test session pass, including the ten new rejection lemmas.
The standalone renaming theory also passes with only its framework import.

All generated exports are byte-identical to the previous verified exports:
398 ordinary modules, 401 RFC modules and 9 relative modules. Clean compilation
reproduced all three production binaries byte-for-byte. The compact suite passed
208 positives, 408 semantic negatives, production/HPC agreement and all 45,733
retained obligations. The frozen 45,753-obligation denominator still records the
20 previously retired counters separately. No timing outliers were flagged.
Focused CLI checks and both legacy and aggregate build-directory entry points pass.

`uncovered-refactor-verification.json` summarizes the gates;
`uncovered-refactor-evidence.json.gz` retains source identities, commands, results,
per-theory/export/compilation timings, original failed attempts and the workspace
mount interruption. `uncovered-relocations.json` maps historical source paths to
the new locations without rewriting frozen evidence. `uncovered-guard-inventory.json`
keeps the supplemental formal tests separate from genuine replay coverage.

The prior fresh 3,484-root replay evidence is reused because the clean-built
checker is exactly the same binary. This follow-up did not run another fresh
Ferrum campaign. HPC is likewise reused only after exact export and adapter
identity checks. No parent worktree, deployment or branch merge was changed.

Genuine relative-ADP processor and positive outermost RZ replay coverage remains
absent. A formal proof refactor and exact generated-code equivalence can verify
this change without pretending to supply those missing replay observations.
No theorem or problem criterion is removed or conflated. Historical uncommitted
development variants remain outside the pinned source scope.
