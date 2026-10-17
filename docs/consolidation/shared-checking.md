# Shared root and residual checking

This batch continues theorem consolidation from `7e9ac72`. Relative ADP and
outermost-RZ development is deferred at the user's request. Their frozen
integration targets remain regression checks; no new snapshots or changes from
those feature families are imported.

## What is shared

The executable processor engines already serve both constructed root problems
and residual obligations. This batch changes proof implementations, not the
checker definitions, guards, parser, certificate representation or CLI.

| Problem | Shared executable engine and soundness interface | Boundary retained |
| --- | --- | --- |
| Nonminimal CSR | `check_csr_dp_termination_proof_core`, its `_sound` theorem | Standalone nonminimal checking rejects processors that need minimality. |
| Minimal improved CSR | `check_guarded_improved_csr_dp_proof`, its `_sound` theorem | Root construction establishes coverage; a residual pair set can be smaller. Both retain well-formedness and symbol freshness. |
| Typed innermost MU-TERM | `check_muterm_i4_root_proof`, its `_sound` theorem | Despite its historical name, the engine also checks standalone typed obligations. Exact unhiding, minimality, signature and replacement-map conditions remain explicit. |

`plain_csr_dpp_mk_context` now supplies the common representation argument at
nine sites: three extended CSR root cases, two guarded CSR root cases, two
expanded MU-TERM adapter cases, and both minimal/nonminimal standalone CSR
cases. It proves plainness and the exact rule/pair projections of the constructed
record. It does **not** prove construction coverage or identify minimal and
nonminimal chain semantics. This is a representation lemma shared by distinct
soundness theorems, not a new acceptance criterion.

The audit is scoped to these paths. It does not assert that every theorem in the
repository is unique, or that every root wrapper can be replaced by a standalone
wrapper. Root coverage arguments and problem-specific bridges still have their
own premises.

## Other theorem consolidation

`not_SN_rel_min_endpoint_tail` extracts the common infinite-chain argument:
under the shared ordering assumptions, a nonterminating minimal chain has a
tail whose pair events are all non-strict. Both lookahead deletion and alternating
strictness use this lemma. Lookahead still requires residual termination;
alternating still requires the next pair to be strict. Their original theorem
statements are unchanged. The ordinary endpoint corollary continues to use the
lookahead theorem.

`muterm_innermost_ur_closed_pairs_subset` and `rhs_mu_vars_condition_subset`
factor restriction to a smaller pair set. The first keeps the ambient rule set,
usable rules and replacement map fixed. It does not assert that changing usable
rules, ambient normal forms or the replacement map preserves safety. Full and
innermost usable-rule criteria remain distinct.

## Verification and limitations

`shared-checking-audit.json` records 180 unchanged existing theorem statements,
unchanged executable declarations in all six changed theories, nine shared
representation call sites and the existing common checker routes. The source
check is lexical; Isabelle checking supplies formal verification.

See `shared-checking-verification.json` and its compressed evidence archive for
build, export, compilation, compact-suite, timing and source identity results.
Runtime coverage does not execute Isabelle proofs. Genuine relative-ADP processor
and positive outermost-RZ replay gaps remain deferred. The frozen full replay has
3,484 roots; reuse of that result requires exact checker identity and does not
constitute a fresh audit of another thread's current frontier.

## Initial patch series

`upstream-proof-series/` contains five reproducibly generated draft patches
against the pinned consolidated prerequisite `85b6876`. The series includes the
preceding finite-coverage/rank specialization and this batch, separated by feature.
Its manifest records exact patch/tree hashes and sequential apply verification.

This starts extraction; it is not yet a complete upstream-ready series against
CeTA 3.9. Feature prerequisite reconstruction and an independent build of that
series remain outstanding. The patch files contain no relative-ADP or outermost-RZ
changes. `tools/consolidation/prepare_proof_series.py` uses a private index without
checking out or moving any branch.
