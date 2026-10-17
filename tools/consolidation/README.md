# Isolated certification regression tools

Run these commands from the consolidated worktree. They never deploy a checker
or modify a parent worktree. Private builds, full corpora and logs belong under
`target/`, which is deliberately excluded from Git.

The committed `tests/certification/harness-smoke` data validates the harness:
eight genuinely regenerated proofs and seven semantic mutations. It is **not**
the minimized full-corpus suite or evidence of complete processor coverage.
`tests/certification/category-smoke` adds four selected relative/outermost roots
and two order-related mutations from six independently regenerated official
inputs. Its instrumentation is the optimized build; do not mix its counters
with the earlier smoke suite's unoptimized instrumentation.

```
python3 tools/consolidation/test_harness.py
python3 tools/consolidation/suite.py \
  --manifest tests/certification/harness-smoke/manifest.json \
  --checker /absolute/path/to/ceta \
  --output target/smoke-check
```

The output directory must be new. Every positive is hash-checked, audited against
its original input, and checked twice. Negatives must be well-formed and rejected
with the intended semantic diagnostic. Crashes, timeouts, parse failures and
acceptance with assumptions do not pass. To check executable coverage, also pass
`--hpc-checker` and `--export-tix`; module identities must match the frozen
denominator. A production-only run does not claim coverage preservation.

The full workflow is `freeze_inputs.py`, `corpus.py`, `oracle_audit.py`,
`replay.py`, `select_suite.py`, `mutations.py`, `pack_suite.py`, then `suite.py`.
See each script's `--help` and the pinned snapshots in `docs/consolidation`.
`recheck_hpc.py` can repeat instrumentation gates in a separate stage while
preserving the original failures. It cannot repair a failed production check or
input audit. Build commands are recorded by `run_logged.py` with elapsed time,
return status and the total-minus-available memory launch gate.

`replay.py` accepts explicit checker binaries, source identity and frozen input
manifests for final replays. `join_stages.py` unions only completed, disjoint root
sets with matching source, oracle, checker and profile identities. A failed or
interrupted stage cannot silently enter that union. `root_audit.py` additionally
checks strict/weak rule partitions and outermost strategy without changing the
vendored original auditors. `map_coverage.py` links changed declarations to HPC
function positions and lists unobserved or unmapped declarations explicitly.

`reconcile_replays.py` can account for failed roots using separately verified
replays with calibrated search budgets. It requires exactly the failed root
identities, unchanged inputs/outcomes and pinned binaries/oracle, and preserves
all original failures. Only the native-action time scale may differ. Stage
joining requires `--allow-time-budget-differences` for that case and records the
effective scale per root. Packaged regeneration preserves those settings.

`coverage.py` distinguishes structural CPF observations from theorem coverage.
Its lexical parser/checker links require review; exact nested semantic states
remain explicit gaps. Unknown nodes must not be silently removed from the
denominator. `setcover.py` minimizes observed obligations without an arbitrary
root cap and reports whether its cardinality bound proves minimality. Secondary
runtime and storage optimization is bounded and does not imply a proof of
optimality.

`performance.py` investigates reported slowdowns with a warmup and alternating
reference/candidate repeats. It verifies binary and certificate identities and
requires successful certification on every repeat. A median slowdown above 20%
remains a failing performance gate, with all measurements retained.

The `vendor` root-correspondence auditors are copied unchanged from the frozen
Ferrum producing revision `b8b572ffba7dbb68f1ec58ef4ff918189f760a83` (its
`scripts/audit_trs_root_correspondence.py` and
`scripts/audit_csr_root_correspondence.py`). They check original problem
correspondence independently of checker acceptance. Source archives, oracle
identities and checker identities are recorded in the snapshot manifests.

The full baseline uses a freshly built pinned Ferrum and frozen search-only
oracle. Neither prior certified status nor a matching benchmark name alone is
enough to admit a proof. Full baseline/final replay and criterion-level mapping
remain mandatory before claiming consolidation complete.
