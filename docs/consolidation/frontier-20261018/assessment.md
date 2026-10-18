# Second frontier integration

The source archive freezes the modified and untracked files of the development
worktree at its recorded HEAD. It does not certify uncommitted sources. Only
selected production theories are integrated, using the consolidated single-parse
CLI and private build outputs.

Two new criteria require distinct feature commits:

* Root-sensitive ADP graph estimation: preserve marked roots across non-root
  base steps, restrict the existing overapproximation by root compatibility,
  and instantiate the graph processor's successor-bounds and edge-coverage
  obligations. Both graph modes retain child-count and function-rooted-LHS guards.
* Filtered derelatification: simulate ordinary nonminimal DP chains through
  argument filtering. Connecting rewrite steps may disappear, but DP steps
  remain. This does not establish a minimal-chain or innermost criterion.
  Reuse ordinary DP checking with the explicitly nonminimal problem interface.
  Existing unfiltered certificates use the empty (identity) filter.

The development generic graph module duplicates 1,700 lines of the old fixed
estimator. Consolidation retains one generic implementation with explicit
estimator obligations and a compatibility instance for the original estimator.
Its 16 executable definitions are unconditional top-level functions; the locale
contains only the bounds/coverage assumptions and soundness proofs. Both modes
call the same generated graph-candidate function with different estimators.
The root and recursive contexts continue to use one ADP proof dispatcher.

Both new capabilities pass all six production formal targets and regenerate
the integrated Haskell checker. The compact suite passes 208 positive proofs
twice and 408 semantic rejection cases, with agreement from the HPC binary.
All 688 newly uncovered campaign certificates pass twice with original-input
correspondence. The previous 48 frontier proofs, 19 new/boundary fixtures, and
36 graph/filter mutations also pass their intended checks. The original 3,484-proof corpus also passes. Joining exact root, proof hash,
input hash, and answer identities covers all 4,176 roots in the frozen available
frontier without losses. The latest SRS225 report lacks details, so the frozen
inventory uses the last available SRS206 report. Independent reconstructed-series
build results are recorded with the series artifacts.
Supplemental certificates are not fresh witness-free oracle-only replays unless
their generation provenance is audited.

The term-root predicate is a refinement of the original tcap estimator. Existing
`relativeAdpDependencyGraph` certificates retain the original estimator and child
ordering. Substituting the new tag into 26 older real certificates changes their
child obligations: 25 fail the child-count guard and one fails a main-index guard.
These derived mutations are not genuine replay evidence. The original 26 proofs
remain valid. The new campaign has 18 unchanged real certificates combining the
new graph estimator with 194 nested filtered-derelatification steps.

The source series is reconstructed against pinned main `e52c7ce`, the starting
prerequisite of this consolidation. It includes the entire consolidation delta,
not only proof simplifications. Reconstruction of the inherited pre-consolidation
history against downloaded CeTA 3.9 is a separate scope; no upstream-ready 3.9
claim follows from exact application of this series.

The new capability commits are `ca0ad20` (shared root-sensitive graphs) and
`996092b` (filtered derelatification). Session-parent reuse and the empty-weak
input audit are separate commits `1acdf97` and `a52e09b`.
