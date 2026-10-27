# Unified production CeTA, 2026-10-26

The stable entry points used by the frozen 5,412-root, 14-category frontier are now
linked into one native executable. `make ceta` builds it; the separately named
legacy entry points remain available for development. No subprocess checker is
used by the unified dispatcher.

The architecture is a small `Main_Unified.hs` plus seven category adapters, each
backed by an independently cached GHC library. See
[`tests/unified/README.md`](../../tests/unified/README.md) for invocation examples,
source snapshot provenance, independent-update instructions and integration limits.
The categories are CPF rewriting, cycle rewriting, conditional rewriting,
conditional erasure, LP (including cut), higher-order, and higher-order delegation.
The 14 benchmark category names map to these entry points; they are not 14
independently competing termination checkers.

All generated modules and the dispatcher are compiled with `-O2`. The existing
higher-order and conditional-erasure scripts now also default to `-O2`. The old
benchmark mixed optimization levels and must not be described as a uniformly
optimized comparison. Lean-generated project C objects were separately audited:
all 1,246 recorded object traces use `-O3`; LeTA has not been downgraded.

`build.json` records the compiler, commands, source identities and library archive
hashes. The native executable's SHA-256 is
`3eba608f0ea41a6f76cc85986fcc16d3edf05da53812dab30eeb148fff141673`.
The normal Make target and the cached rebuild produced that same hash. Cached
rebuilds reused all seven category libraries and relinked the small dispatcher.
`adapter-equivalence.json` checks that each adapter preserves its source driver's
logic exactly, except for module/export declarations and the `withArgs` wrapper.
No Isabelle theorem or acceptance criterion was changed by this integration.

## Results

The authoritative run certified **5,412/5,412** roots in **357.96 seconds** with
32 workers, with no root losses or verdict mismatches. All **408/408** semantic
negatives reject as intended. This elapsed time is validation timing, not a new
controlled CeTA/LeTA speed comparison.

## Validation protocol

The authoritative run is `frontier-final.json.gz`: 32 concurrent workers, one
certification of each original frozen input/proof identity, expected verdicts taken
from the pinned production results, and a single immutable checker binary. This
is certification only, without Ferrum search or regenerated proofs. The runner
verifies certificate/input/child hashes and the exact final root set. It includes
all 363 pure-LP roots, 91 LP-with-cut roots, 228 higher-order roots, 200 cycle roots,
and every other retained rewriting-category root.

`negatives.json.gz` rechecks all 408 retained CPF semantic negatives using their
intended diagnostic, not merely a nonzero exit code. Four historic diagnostic
regexes predated the typed MU-TERM checker: their current messages explicitly
identify missing dependency pairs. Those four messages were compared with the
pinned production checker and are unchanged by this integration; the exact
mutation hashes and messages are retained in `negative-diagnostic-updates.json`.
All 408 give the intended semantic rejection. Dispatch tests additionally reject
unknown categories, malformed certificates and invalid invocations. They are not
counted as semantic negative coverage for the new categories.

The first full run was invalidated: a cache-rebuild experiment relinked the binary
while validation was running, causing 25 launch errors and a final hash-guard
failure. Its journal is retained for audit and excluded from acceptance. The build
now atomically replaces the executable after linking, and the runner freezes an
immutable, hash-named copy before launching any checks. The clean final run is the
only run used for the final single-binary coverage claim. This explains the extra
full pass; it was not an unexplained certificate rejection or repeated search.

## Reproduction

```
make ceta CETA_UNIFIED_BUILD_DIR=target/unified-o2-20261026 \
  CETA_BIN_DIR=target/unified-release
python tests/unified/check_dispatch.py target/unified-release/ceta
python tests/unified/check_negatives.py target/unified-release/ceta \
  --output target/unified-o2-20261026/negatives.json.gz
python tests/unified/check_frontier.py \
  --binary target/unified-release/ceta \
  --provenance ../CeTA-Lean/target/production-certification-benchmark-20261025/provenance.json \
  --baseline-results ../CeTA-Lean/target/production-certification-benchmark-20261025/ceta.json.gz \
  --archive ../CeTA-Lean/target/corpus/frontier-5412.zip \
  --output target/unified-o2-20261026/frontier-final.json.gz --workers 32
```

The corpus archive is identified by its hash, so it can be relocated using the
arguments above. The build itself uses the committed generated-code archives and
does not depend on mutable export paths. The higher-order child proofs are also
retained as a compressed, hash-checked archive. This native integration of verified
exports does not claim to rerun every originating Isabelle session or merge later
unreviewed development theories. Other worktrees' production checkers and oracles
were not replaced.
