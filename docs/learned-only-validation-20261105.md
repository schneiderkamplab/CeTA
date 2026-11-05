---
type: Experiment Report
title: "Unified CeTA in reconciled learned-only validation"
status: stable
---
# Unified CeTA learned-only validation

The reconciled Ferrum package certifies **6,570/6,816** inputs,
retaining all **6,565** required learned root/polarity pairs. Every acceptance
has original-input correspondence and **two successful checks** by the same
unified CeTA executable. All fifteen recorded matched category comparisons
show coverage superiority; the cycle comparison remains a separate historical
population. [Ferrum report](../../ferrum-learned-release/docs/learned-release-validation-20261105.md)
and [immutable evidence](../../ferrum-learned-release/docs/data/learned-release-validation-20261105.json)
record the exact scope, unresolved inputs, failed intermediate gates and hashes.

CeTA checking logic did not change during reconciliation or subsequent
scheduling repairs. The isolated tree `CeTA-learned-release`, branch
`codex/learned-release-20261105`, merges main `09a5052` and verified export
`d2e6e66` as source commit `dde8fb1ad08bf826f4f60fa57a73b3190dd2aba6`.
Only the documentation index required conflict resolution. The preceding
formal source is `39f3374`; see [recursive RFC checking](rfc-recursive-residuals.md).
Generated checking logic was not patched.

The fresh unified O2 build has executable SHA-256
`d19704667ae17f6f6154d8b729e800a0ee15cfac416d26779534779c26062113`.
Every accepted category uses that immutable binary. Ferrum runtime source is
`47a474a`, binary SHA-256
`a6aabe39c56a126063460adaa4fea0bd696f7c9edfe0fc569ceb2c9d1ee52daa`;
reconciled harness `f5ab2d2`; final evidence commit **`83bf38a34258d36c98c3ec9fbf09d38ce3a2c32c`**.
The one category-policy package has manifest SHA-256
`2007ff268cbb4fd9e8fc3d2b3f4da7e036c16249610d23579c9088db2ea85721`. Its eleven native profiles select advice by typed category and
state features, not by root membership. Production oracle bytes and format
remain unchanged and unused:
`3adcaf4d4aaea28af9b97adf282e24173ea9477bfec87ae083048c99329e5cbb`.

The fresh `combined-isolated` replay uses 96 workers, four logical CPU slots per
worker, 300-second search/per-check limits and the recorded competition memory
limit. Its explicit 368-slot pool excludes six physical cores occupied by
external pinned jobs; unavoidable overlap is audited. Wall time is
933.032 seconds. This establishes certified coverage within those
limits, not a speed comparison. The final evidence identifies source, certificate,
policy, executable and environment hashes and records actual worker placement.

This milestone does not change main, integrate ongoing Prolog work, provide
CeTA-Lean ITS coverage, or complete the independent two-checker release.
The [binding architecture links](state-local-integration.md) remain authoritative.
