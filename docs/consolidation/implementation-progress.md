# Implementation evidence after approval

The user approved proceeding beyond the assessment checkpoint. Work remains
isolated on `consolidated`. The full baseline replay, compact regression suite and isolated Isabelle/export/compile
baseline pass. The pinned mains are reconciled and committed, and all four
Isabelle targets pass. The reconciled focused, compact and full-corpus gates pass. The pinned-main
reconciliation is committed as `a485775`. The assessment document describes its earlier checkpoint;
this document records subsequent implementation evidence.

## Passing committed infrastructure

The harness smoke suite retains eight genuinely regenerated original roots and
seven semantic mutations. An additional category suite selects four roots from
six fresh relative/outermost replays, with two order-related mutations. Both
suites pass original-input correspondence, twice production checking and their
respective HPC coverage gates. The harness tests also reject changed relative
partitions and lost outermost strategy. See `harness-verification.json` for the
scope and results; these small suites are not the final compact corpus.

The source archive, complete search-only oracle and private LP dependencies are
durable under `tests/certification/replay-assets`. A fresh build from those assets
regenerated all eight original smoke roots and certified them twice. The assets
do not depend on mutable parent campaign paths. Toolchain prerequisites and
identities are documented beside them.

## Full baseline partitions

The original frozen corpus contains 3,478 distinct roots. All retained candidate
certificates matched their receipt hashes and original ARI inputs, but fresh
replay is still required for eligibility. Six explicitly snapshotted official
relative/outermost inputs extend the prospective full baseline to 3,484 roots;
their identities appear in `category-supplement.json`.

The first full replay used unoptimized HPC instrumentation. Large certificates
passed production twice but repeatedly exhausted that instrumentation's
600-second ceiling. A separately built optimized checker passed all 269
completed roots, including the timed-out cases. Original failures remain in
`target/consolidation-corpus/baseline` and `baseline-o2`.

Only this task's original replay orchestrator and its verified private process
groups were stopped. The interruption receipt is
`target/consolidation-build/baseline-interruption.json`. The complete 269-root
partition is retained in `baseline-completed-o2`; all other 3,209 original roots
are freshly replayed in `baseline-remaining-o2`. `baseline-extra` contains the six
supplemental roots. Their union must match the exact 3,484-root inventory before
the final coverage denominator is frozen. Interrupted work is not a pass.

Three later fresh replays returned `Unknown` after internal match-bounds action
budgets expired. Separate replays with the same rebuilt source and oracle at a
larger time scale regenerated all three proofs, passed original-input audits,
production twice and optimized HPC. `search-budget-calibration.json` records
these results. Their original failures remain retained. The final baseline
must reconcile every failed identity and freeze effective per-root time budgets;
simply excluding the failed attempts from the root set is forbidden.

## Frozen regression baseline

All 3,484 roots have fresh eligible replays with exact input/root/answer
correspondence, twice production certification and optimized HPC agreement.
The three calibrated recoveries are explicitly reconciled; none is dropped.
`baseline-root-evidence.json.gz` retains per-root evidence. All original inputs
and the full replay manifest are durable in `tests/certification/replay-assets`.

The compact suite contains 208 positives and 408 validated semantic negatives (including
24 subsequent GM04 freshness-collision tests).
Its 45,753 observed structural/executable obligations are frozen. The optimizer
proved minimum cardinality (207 unsatisfiable, 208 satisfiable); secondary timing
and storage optimization was bounded. Compressed positive storage is about
6.3 MB, with measured baseline single-pass checking around 36 seconds.
The complete compact run passed acceptance and exact HPC coverage. Six timing
outliers passed controlled interleaved repeats with no confirmed slowdown.

The changed-source mapping observes 107 of 245 indexed checker declarations.
Zero unknown proof nodes were found. This does not establish full criterion
coverage: nested semantic states, uncovered declarations and side conditions
remain explicit gaps and constrain which restructuring is justified.

## Coverage limits and gate history

The isolated Isabelle build covers ordinary integration/export, absolute RFC
and relative ADPs with private dependencies/heaps. All baseline Isabelle integration/export targets and separate ordinary, RFC
and relative-ADP binaries have passed. The reconciliation and export/build cleanup batches are verified below. Complete semantic context mapping remains partial. Preliminary source/HPC links are
candidate mappings, not a claim that runtime tests execute Isabelle proofs.

Relative contexts now have genuine evidence, but these two proofs use ordinary
polynomial/matrix rule removal, not relative ADPs. The four outermost proofs are
nontermination proofs, not positive coverage of the RZ transformation. Those
criteria remain explicit coverage gaps and are not authorized for unverified
restructuring by this evidence.

## Reconciled source and timing investigation

The verified source tree `ab4a952a905c7bbd6ac1ebb92e5340b67378303c`
preserves the general CeTA-main innermost GM04 adapter and the CSR-main full
and nontermination constructors. All other production theory/parser changes
are exactly the pinned CSR-main source. No theorem or problem variant has been
retired. All four Isabelle targets passed in 2,281.8 seconds; separate ordinary,
RFC and relative binaries compile, and focused checks pass. Fresh exports replace
tracked generated Haskell, including the previously stale relative module.

The timing harness now measures child completion without POSIX timed-wait
polling delay. A process-group watchdog preserves timeout behavior and has an
explicit child-process cleanup regression test. The original apparent slowdown
is retained in `baseline-timing-investigation.json.gz`; nine interleaved repeats
with precise timing found no production or HPC slowdown above 20%.

Coverage migration retains the original 45,753-obligation denominator. The
reviewed transition maps 44,790 executable obligations and explicitly retires
20 counters for the removed innermost-only C/variant computations and their
continuations. Retirements are never counted as executed coverage. The 943
structural obligations remain required. Initial identity validation correctly
rejected omitted zero-counter modules; `coverage-inventory-recovery.json`
records that harness failure and its correction.

The reconciled compact gate now passes all 208 positives twice, all 408 semantic
negatives twice, and production/HPC agreement including negative rejection.
It observes all 45,733 retained original obligations, with exactly 20 separately
reported retired counters and no missing retained coverage. One initial HPC
microbenchmark outlier did not persist in 41 interleaved repeats, including a
CPU-affinity-controlled run. All timing attempts remain in
`reconciled-compact-evidence.json.gz`. Legacy split-input CLI forms certify;
an unknown proof node remains unsupported, not accepted.

`processor-mode-coverage.json.gz` connects 193 observed syntactic modes across
58 processor tags to selected real positives, 408 semantic negatives and
parser/checker/theorem candidates. Thirty modes have directly targeted negatives.
The standalone bounds adapter is absent from the lexical registry; its one
negative and source-reviewed `bounds_tt` connection remain explicitly separate.
This supplemental inventory does not silently alter the frozen denominator or
claim that every candidate theorem link has a reconstructed semantic state.

The full retained-corpus recheck passed all 3,484 exact original root/input/answer
identities, with twice production checking and HPC agreement, in 2,710.0 seconds.
There are no losses. `reconciled-corpus-evidence.json.gz` retains every result;
`reconciled-verification.json` summarizes the completed reconciliation gates.
The export cleanup and fresh final replay are the subsequent batch/milestone.

## Verified export/build cleanup

The cleanup source tree is `d2ce39d43bf411e290ad4cd0d462dbcad5686650`.
All four Isabelle integration/export targets passed, and ordinary, RFC and
relative generated modules are byte-identical to the reconciled exports.
The relative comparison accounts explicitly for its eight existing helper
modules; an initially incomplete expected-file list is preserved with its
correction. No checker/theorem criterion changes in this batch.

Shared Haskell configuration now has one source with compatibility imports.
`Code` inherits `Proof_Checker`, while legacy aggregate sessions remain
available. Relative export uses Isabelle's export store instead of writing into
the source tree. Hand-written CLI adapters live in `src/Haskell`, with separate
ordinary/RFC/relative binaries and object directories. Relative compilation no
longer overwrites the primary `ceta`. The 358 generated-directory AppleDouble
sidecars are removed; future sidecars are ignored.

The new Makefile built all three CLIs in 271.4 seconds; HPC compiled separately
in 99.9 seconds. The compact suite again passed 208 positives, 408 semantic
negatives, production/HPC agreement and all retained coverage. Forty-one
interleaved CPU-affinity-controlled repeats resolved the short-run timing
candidates without a slowdown above 20%. `cleanup-verification.json` and
`cleanup-evidence.json.gz` record the gates. The fresh 3,484-root final replay passed from durable assets against this frozen source tree, as recorded below.

## Final acceptance of the verified scope

Production changes are committed in `a485775` (pinned-main reconciliation) and
`bcc0f51` (shared exports and isolated build outputs). All work stays on the
`consolidated` branch; no parent deployment or merge was performed.

The final fresh Ferrum replay passed all 3,484 frozen root/input/answer identities,
with original-input correspondence, twice production certification and optimized
HPC agreement for every proof. There are no certified-root losses. Of the proofs,
3,455 are byte-identical to baseline; the other 29 were parsed again. No unknown
nodes or new unreviewed structural obligations were found. All 45,733 retained
obligations were observed; the original 45,753 denominator remains recorded with
20 explicitly retired obsolete counters, never counted as executed coverage.
See `final-verification.json` and `final-replay-evidence.json.gz` for the exact
comparison, per-root commands, identities, results and timings. Replay search
times vary; the maximum final search was 952.1 seconds, within its frozen ceiling.

The committed source was compared blob-by-blob with the verified private build.
All four Isabelle targets revalidated against private heaps. A clean GHC rebuild
reproduced all three production binaries byte-for-byte. An earlier incremental
relink differed in GHC temporary FILE symbols and derived build IDs only; that
failed equality assertion and its investigation are retained, not counted as an
identical build. `committed-build-verification.json` and
`committed-build-evidence.json.gz` record both outcomes.

The 208-positive/408-negative compact gate passes, including HPC semantic
rejections and retained coverage. Controlled repeats found no confirmed compact
checker slowdown above 20%. No theorem or problem variant has been retired.
Relative ADP positive replay coverage, positive outermost RZ coverage, and complete
nested semantic-state/theorem mapping remain gaps. Semantic restructuring of
those paths is deferred as required by the plan; build/integration verification
does not fill their missing positive coverage. The feature-by-feature upstream
outline is `deferred-upstream-series.md`; reconstructing that patch series remains
outside this consolidation.
