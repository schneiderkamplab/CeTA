---
type: Implementation Plan
title: "State-local checker integration"
status: draft
---
# State-local checker integration

The authoritative [Ferrum architecture contract](../../ferrum/docs/architecture.md) governs this implementation. Follow its [processor](../../ferrum/docs/processor-contract.md), [identity](../../ferrum/docs/state-identity.md), [guidance](../../ferrum/docs/guidance-contract.md), and [release](../../ferrum/docs/release-gates.md) contracts.

The snapshot starts at CeTA main 6ce5ab3. Historical unified ITS validation is retained under `unified-its-20261027/`. No checker logic changed in this milestone. Preserve the independently built unified executable and verified libraries; fix stale callers rather than substituting category executables. Regenerate affected exports from Isabelle. Release evidence must bind every category to one immutable executable hash.

The full architecture release has not passed: independent CeTA-Lean ITS coverage and the new 15-category two-checker replay remain open. Cross-repository links target the maintained sibling Ferrum checkout; release evidence must pin the repository revisions. CeTA checking logic and the installed executable remain unchanged.


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
