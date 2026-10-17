# Implementation evidence after approval

The user approved proceeding beyond the assessment checkpoint. Work remains
isolated on `consolidated`; no semantic theory, checker, parser or generated
Haskell change has been made yet. The prerequisite full regression baseline is
still in progress. The assessment document describes its earlier checkpoint;
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

## Gates still pending

The isolated Isabelle build covers ordinary integration/export, absolute RFC
and relative ADPs with private dependencies/heaps. The full replay, final set
cover, complete semantic context mapping, additional paired negatives and
consolidation batches are still pending. Preliminary source/HPC links are
candidate mappings, not a claim that runtime tests execute Isabelle proofs.

Relative contexts now have genuine evidence, but these two proofs use ordinary
polynomial/matrix rule removal, not relative ADPs. The four outermost proofs are
nontermination proofs, not positive coverage of the RZ transformation. Those
criteria remain explicit coverage gaps and are not authorized for unverified
restructuring by this evidence.
