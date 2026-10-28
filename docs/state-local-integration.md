---
type: Implementation Plan
title: "State-local checker integration"
status: draft
---
# State-local checker integration

The authoritative [Ferrum architecture contract](../../ferrum/docs/architecture.md) governs this implementation. Follow its [processor](../../ferrum/docs/processor-contract.md), [identity](../../ferrum/docs/state-identity.md), [guidance](../../ferrum/docs/guidance-contract.md), and [release](../../ferrum/docs/release-gates.md) contracts.

The snapshot starts at CeTA main 6ce5ab3. Historical unified ITS validation is retained under `unified-its-20261027/`. No checker logic changed in this milestone. Preserve the independently built unified executable and verified libraries; fix stale callers rather than substituting category executables. Regenerate affected exports from Isabelle. Release evidence must bind every category to one immutable executable hash.

The full architecture release has not passed: independent CeTA-Lean ITS coverage and the new 15-category two-checker replay remain open. Cross-repository links target the maintained sibling Ferrum checkout; release evidence must pin the repository revisions. CeTA checking logic and the installed executable remain unchanged.

## Existing triple checkers connected to the unified adapter

Revision `3344eae` connects the already exported initial and return-family triple
checking functions to the LP adapter. No generated module, Isabelle theorem or
export archive changed; all other category libraries retain their hashes.
The isolated O2 binary is
`b4165eefc964f4417cb184cc4545f7437dbcfd2acacca15f2f7ed122c6406a52`.
The installed main executable is unchanged. The candidate passes 49 retained
LP/cut positive certificates and 49 negatives, plus dispatch rejection tests.
Ferrum `7a7fc41` separately passes six fresh initial-triple proof runs with two
checks each and six semantic mutations. Return-triple families still require
fresh per-family migration gates. The full-frontier gate remains open.
[Recorded regression checks](data/lp-triples-dispatch-3344eae-validation.json)
and the private build at `target/unified-lp-triples` retain the evidence.

## Finite LP artifact dispatch

Revision `54a99ee` adds the existing Isabelle-generated finite-LP checker to the
same LP library and unified dispatcher. The imported export is byte-identical
to the verified `lp-finite-production-v2-20261021` snapshot; its four recorded
LP theory files are byte-identical to the current checkout. The preserved
[export identity](data/lp-finite-export-20261021-identity.json) records its source
revision and parent environment. No existing generated module was edited, and
other category libraries retain their archive hashes.

The isolated O2 executable at `target/unified-lp-finite/ceta` has SHA-256
`c89d366b2d2c57d73f8fe13157975882814a0af1cff2ebba6584bfbfdb9e0f44`.
It passes 346 positive checks and 81 negative checks, including all 91 retained
cut roots, plus the finite-artifact and unified-dispatch regression tests.
[Validation evidence](data/lp-finite-unified-54a99ee-validation.json).
The previous `b4165eef...` candidate and main executable are preserved. This
is a checker-library regression gate, not a new full-frontier replay.
