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

The frozen full-corpus compact suite is now `tests/certification/compact`: 208
positives and 408 semantic negatives. Run it with the same `suite.py` interface.
Its denominator covers all observed eligible baseline obligations; uncovered
semantic paths remain gaps, not evidence supporting removal.

`recheck_corpus.py` checks every frozen certificate twice against a new binary
and compares exact root/input/answer identities. Matching proof and input hashes
allow reuse of the frozen correspondence audit; `--reaudit-inputs` repeats it.
Optional HPC checking writes new coverage without replacing old evidence. This
is a corpus gate, not a substitute for fresh Ferrum regeneration.

`coverage_delta.py` maps unchanged spans or literal-preserving token sequences
with identical HPC labels (monotone alignment or expressions unique in both
module versions)
across exports. Every required counter it cannot map is reported with its source
expression. It never automatically retires obligations or approves a changed
criterion. An identity comparison maps all 44,810 observed executable baseline
counters; the remaining 943 baseline obligations are structural observations.

Coverage migrations require an explicit `--coverage-transition` file. It pins
the old denominator and new checker/HPC binaries, accounts for every original
executable obligation, and reports retired counters separately from observed
coverage. Changed enclosing expressions require recorded source review. Empty
modules are included in `export-mix --modules DIRECTORY`; they are not ignored.
Negative proofs also require the intended semantic rejection from HPC when
instrumentation is enabled.

`performance.py --instrumented` investigates positive HPC timings. Production
repeats include semantic negatives. The process runner blocks on completion and
uses a cancellable process-group watchdog; older timed-wait polling measurements
are retained but can include up to 50 ms of observation delay. Investigations
must compare both binaries with the same current measurement method.

`build_verified.py` is the clean-build recipe for the export-cleanup layout:
pass a committed `--revision`, external `--isabelle`/`--ghc` installations and a
new `--output` directory. It extracts the committed source and exact AFP archive,
uses private Isabelle settings/heaps, builds all four production targets plus
the outermost RZ rejection-test session, exports
ordinary/RFC/relative code and compiles three separate CLIs plus HPC utilities.
It does not deploy binaries or use another campaign's writable heaps.

`compare_replay.py` compares a fresh packaged full replay with exact frozen root,
answer and input identities and the reviewed coverage transition. Byte-identical
proofs may reuse structural analysis from the durable baseline matrix; changed
proofs are parsed again. Unknown nodes, missing retained coverage and newly
unreviewed structural obligations are explicit failures requiring investigation.

`audit_retirement.py` records the eight preserved theorem interfaces and their
lexical callers for the theorem-retirement batch, plus retained semantic
contracts. It checks unchanged guarded executable declarations. The accompanying
Isabelle/export evidence is required: this source audit alone does not prove
equivalence or acceptance. Missing genuine replay coverage is reported separately
from formally justified semantic specialization.

`audit_sharing.py` checks the preserved theorem statements and executable
interfaces for the root/residual sharing batch and records its common call sites.
`prepare_proof_series.py` emits five draft proof-only patches against a pinned
consolidated prerequisite. It uses a private index and exactly checks sequential
application without moving branches. This is not an independent build of the
series or a complete upstream CeTA 3.9 prerequisite reconstruction.
