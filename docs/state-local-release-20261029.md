---
type: Report
title: "Unified checker full-frontier release 2026-10-29"
status: stable
---
# Unified checker full-frontier release

The independently regenerated unified CeTA executable at source revision
`0a3cca39bf93b0b43b44d89c95d439e93279d603` passed repeated checks of all
6,526 roots across 15 categories in the strict Ferrum release. Checker SHA-256:
`362c56d7335a60bff89f84c19d54f437be5582fb2e125bb299514d99e0f94fac`.

[Authoritative release report](../../ferrum-state-local/docs/state-local-release-20261029.md)
records the exact Ferrum/oracle/root identities, original-input and receipt audits,
96-worker concurrency, retained evidence and local binary distribution.
[Source-map checker contract](gm04-source-proof-map.md) and
[mutation/dispatch evidence](data/gm04-source-map-20261029.json) remain binding.

This release integrates the `codex/state-local-lp-cut` source into CeTA main.
CeTA-Lean ITS and dual-checker release acceptance remain deferred; this report
claims CeTA validation only. No generated checking logic was hand-patched.
