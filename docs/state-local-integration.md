---
type: Implementation Plan
title: "State-local checker integration"
status: draft
---
# State-local checker integration

The authoritative [Ferrum architecture contract](../../ferrum-state-local/docs/architecture.md) governs this implementation. Follow its [processor](../../ferrum-state-local/docs/processor-contract.md), [identity](../../ferrum-state-local/docs/state-identity.md), [guidance](../../ferrum-state-local/docs/guidance-contract.md), and [release](../../ferrum-state-local/docs/release-gates.md) contracts.

The snapshot starts at CeTA main 6ce5ab3. Historical unified ITS validation is retained under `unified-its-20261027/`. No checker logic changed in this milestone. Preserve the independently built unified executable and verified libraries; fix stale callers rather than substituting category executables. Regenerate affected exports from Isabelle. Release evidence must bind every category to one immutable executable hash.

The new architecture release has not passed: LeTA is unavailable and no new full-frontier replay has run. Cross-repository links reflect the isolated worktree layout; publication must retain resolvable repository revision links.
