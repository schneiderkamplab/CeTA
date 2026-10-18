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

## Authorized refactoring of uncovered paths

After the earlier acceptance milestone, the user explicitly requested refactoring
paths without genuine positive replay coverage. Relative ADP sources now reside
in `thys/Relative_ADP`, with compatible session names and old build-directory
entry points. General injective-renaming proofs are extracted from the ADP
adapter, and the RZ adapter uses an explicit transformation soundness theorem.
Ten new formal rejection lemmas pass. All production integration/export targets,
clean binary identity, focused checks and the complete compact suite pass.

See `uncovered-path-refactor.md` and `uncovered-refactor-verification.json` for
this follow-up's scope and evidence. The genuine replay gaps remain recorded;
the refactor is verified through formal proofs and exact executable equivalence.
The 3,484-root full replay belongs to the earlier milestone and is reused by
binary identity, rather than described as a new campaign.

## Theorem retirement and semantic specialization

The user authorized continuing the retirement assessment. The verified batch in
[theorem-retirement.md](theorem-retirement.md) replaces eight independently
maintained proofs with shared theorems and corollaries, and defines finite
conservative coverage through general conservative coverage with a restricted
replacement map. The old explicit characterization is proved equivalent and
the production refinement migrated. Distinct problem kinds remain explicit;
the report records the contract-based keep/unify decisions.

All affected Isabelle layers and all five integration/export targets pass.
Exports and clean-built binaries are byte-identical. The 208-positive,
408-negative compact suite passes production/HPC agreement and all 45,733
retained obligations. Controlled repeats clear all four timing outliers.
`theorem-retirement-verification.json` and its compressed evidence archive
record the passing gates and the failed preliminary proof scripts separately.
The frozen 3,484-root replay evidence is reused by exact binary identity;
this batch makes no claim about a newly snapshotted current Ferrum frontier.

## Shared root/residual checking and continued theorem consolidation

The batch described in [shared-checking.md](shared-checking.md) replaces nine
copies of the plain dependency-pair representation proof with one shared lemma.
Root and standalone CSR/MU-TERM checking retain their existing common processor
engines and soundness interfaces; construction coverage remains a root obligation.
The alternating and lookahead endpoint criteria now share their infinite-chain
argument, and usable-rule pair-set restriction uses general subset lemmas.
All 180 existing theorem statements in the six changed theories are preserved.

Focused Isabelle checking and all five integration/export targets pass. All three
export sets and clean-built checker binaries are byte-identical to the preceding
verified batch. The compact suite passes all 208 positives, 408 semantic negatives
and 45,733 retained coverage obligations, with no timing slowdown candidates.
`shared-checking-verification.json` and its compressed evidence record source
identity, timings, final passing gates and preliminary proof-script failures.

Five reproducible draft proof-only patches are now extracted and exactly
apply-checked against consolidated prerequisite `85b6876`. This starts upstream
series preparation; it does not reconstruct all prerequisites from CeTA 3.9 or
claim an independent build of that draft series. Relative ADP and outermost-RZ
development remain explicitly deferred. The frozen 3,484-root replay evidence is
reused through exact binary identity; no current-frontier snapshot was taken.


## Frontier snapshot integration

The user reopened relative ADP and outermost-RZ. The isolated snapshot in
[frontier-20261017/assessment.md](frontier-20261017/assessment.md) generalizes the
ADP compound-order criterion, shares its executable guard, adds RFC recursion
through `Split`, and adds the full-termination-to-outermost bridge. The existing
integrated entry point parses each document once and dispatches its parsed proof
to the shared ordinary/RFC or ADP checker. Full-corpus checks exposed input
retention in whole-document fallback dispatch, including the previous integrated
checker; the single-parse integration removes that fallback.
No duplicate campaign checker or test adapter was imported.

All affected Isabelle layers and five integration/export targets pass. Generated
Haskell comes from those verified exports. Both compact entry points pass all
208 positives and 408 negatives; the default HPC run preserves all 45,733
retained obligations without additional retirements. The 48 frozen supplemental
frontier proofs pass twice production checking, HPC agreement, input audits,
separate-input invocation and 74 semantic mutations. The two derived bridge
fixtures are recorded separately and never counted as genuine Ferrum replays.

The full-corpus recheck and final evidence are recorded in the snapshot report.
The workspace outage interrupted the first corpus run; completed results are
reused only after identity/hash checks, and incomplete or failed attempts are
preserved separately. This work does not certify an unsnapshotted moving frontier.

The final [verification report](frontier-20261017/verification.json) passes all
3,484 frozen roots with twice default certification, HPC agreement and an
additional check by the corrected integrated entry point. Exact roots and all
45,733 retained obligations are preserved. On the 2.64 GB regression certificate,
the integrated checker improves from 397.6 seconds / 204 GiB peak RSS to
102.1 seconds / 17.0 GiB. All supplemental and derived tests pass. The frozen
recheck is explicitly distinguished from fresh Ferrum regeneration.
