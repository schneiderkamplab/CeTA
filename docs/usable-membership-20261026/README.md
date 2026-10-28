---
type: Historical Report
---
# Shared usable-rule membership and compact frontier

The executable usable-rule closure check now constructs one set per usable-rule
context and shares it across the usable right-hand sides and dependency-pair
right-hand sides. The existing generated RBT implementation supplies indexed
membership. Previously each relevant subterm scanned the usable-rule list.

`thys/Usable_Rules_Membership/Usable_Rules_Membership.thy` proves equality of the
entire check result, including diagnostics, to the previous recursive checker.
A proved code equation replaces only the parent checker's executable equation.
Replacement maps, argument filters, matching/capping and all soundness
assumptions are unchanged. The existing soundness theorem remains authoritative.
No new proof admission or oracle is introduced.

The optimization is exported into CPF, conditional erasure, higher-order
first-order delegation, and all five LP modules that contain the closure checker.
The other category exports do not contain this checker. Every generated module
and the main executable are compiled with `-O2`. Generated Haskell is never
patched: higher-order module cycles are resolved by Isabelle `code_identifier`
configuration, including the newly reachable character-order instance.

## Source and export provenance

The proof/build uses Isabelle2025-2 and private dereferenced copies of compatible
heaps under `target/usable-membership-20261026`, with identifier
`usable_membership_20261026`. Base theories are the frozen
`target/equational-production-20261019/source/thys` snapshot. No parent production
checker, source, oracle, or dependency heap is modified.

The historical LP v145 build receipt names a revision that preceded some of its
then-uncommitted theories. The later committed LP snapshot
`cd3af45dd2d296f8a60e626e173e24b42574b474` was therefore pinned and recovered.
**All five unoptimized module regenerations match the production modules
byte-for-byte**, as recorded in `lp-reproduction.json`. Shared foreign helper
modules also match unchanged. The indexed exports are separately kernel checked,
including inherited-oracle and skip-proof audits.

`lp-source.tar.gz` preserves that committed LP source snapshot;
`export-wrappers/` contains the actual audited export theories. The first LP
baseline/indexed pair completed in the serial console; its remaining work was
cancelled after the indexed export marker, because the other four pairs had
been assigned independent consoles. The four separate pair receipts record
successful completion. The truncated serial log is retained, not presented as
a completed five-pair run.

To reproduce the LP export pairs, configure an isolated Isabelle user home,
identifier, AFP and private compatible Proof_Checker heap, then run
`tools/consolidation/reexport_usable_lp.py --isabelle ISABELLE --base-theories BASE
--output NEW_DIRECTORY --workers 4`. This checks both baseline and indexed
module hashes against the recorded exports. Saved build/export commands for
CPF, higher-order and conditional erasure accompany this report.

To rebuild the final executable from the committed generated snapshots:

```
python scripts/build_unified_checker.py --output target/unified-usable-membership-20261026
```

## Re-export scope

This is certification-only reserialization of the frozen 5,412-root frontier,
not a new Ferrum search. All 5,283 unique proofs were processed: 4,823 XML proofs
were compacted and 460 non-XML proofs retained byte-for-byte. The 36 delegation
children use the previously verified structural compaction. Significant leaf
text, mixed content, entities, CDATA and `xml:space` are preserved.

Unique primary proof bytes fell from 99,373,967,752 to 18,413,345,128. The export
pass took 293.01 seconds with four workers. The compactor comes from the isolated
Ferrum commit `8336ef2`, executable SHA-256
`572aaf68979ab634622a8bb487f3689e7f46faa2cb06bd4797d9be76f9f1074a`.

The full candidate archive is retained separately at
`target/compact-frontier-20261026/frontier-5412-compact.zip`, SHA-256
`9f92b9b942d70ab36ace3367f7793c8dd2d34ed298900122f64814c73975c63d`.
`compact-manifest.json.gz`, `compact-provenance.json.gz`, and
`reexport.json.gz` retain original/new proof hashes, exact root/input identities,
per-proof sizes and export timings. The original archive remains unchanged.

To repeat compaction, build `examples/compact-child.rs` at Ferrum commit
`8336ef2` (release mode), then run:

```
python tools/consolidation/compact_frontier.py \
  --manifest ../CeTA-Lean/docs/corpus/frontier-5412.json.gz \
  --archive ../CeTA-Lean/target/corpus/frontier-5412.zip \
  --compactor /path/to/compact-child --output target/compact-frontier-new --workers 4
```

This verifies the original archive and each input proof hash and records the
new compactor binary identity. Its byte output uses the same shared Rust
structural whitespace implementation as the production export fix.

## Validation and timings

All 5,412 exact roots accepted with the final executable at 32 workers, one
certification per root. All 408 retained semantic negatives rejected with their
expected diagnostics; dispatcher checks passed. No root/input/answer drift was
found, and every new proof hash is linked to its original proof hash.

Final binary SHA-256:
`8b5e6c3560cf10f1952b68b52931e2e6becac7b8e93f1a19776b277edef3d28c`.

The campaign took 331.73 seconds (previous comparable campaign: 344.25 seconds).
The same compact h31 child certifies in 18.57 and 18.84 seconds versus the prior
67.48 seconds: about 3.6 times faster. This focused comparison holds the
certificate bytes fixed; the campaign also includes primary-proof compaction.

All values below are seconds; p95 and p99 use linear interpolation.

| Measurement | Min | Median | Mean | p95 | p99 | Max |
|---|---:|---:|---:|---:|---:|---:|
| Native checking | 0.011840 | 0.118462 | 0.971335 | 4.068380 | 19.806476 | 86.682649 |
| Preparation | 0.022345 | 0.220358 | 0.235022 | 0.438526 | 0.684454 | 1.156275 |

Maximum native time: `SRS_Standard/ICFP_2010/161533.ari`. Maximum preparation:
`TRS_Standard/Transformed_CSR_04/OvConsOS_complete_noand_GM.ari`.
`frontier-final.json.gz` records all results and per-root native/preparation
measurements; `per-root-times.csv` places old and new timings side by side.

The native mean improved from 1.046668 to 0.971335 seconds, and preparation mean
from 0.294239 to 0.235022 seconds. Native p95/p99 increased in this shared-host
campaign; they are reported rather than hidden by the improved mean and maximum.
Controlled repetitions of the largest regressions are recorded separately.

The proved optimization and generated exports are committed as `f8224d5`.
The benchmark preparation in CeTA-Lean is updated to select the compact primary
archive and this hash-validated all-category executable. This milestone does
not rerun LeTA certification and makes no new LeTA timing claim.

Controlled comparisons used identical compact proofs, three workers, and the
order old/new/new/old. All twelve checks accepted.

| Root | Old mean (s) | New mean (s) | Change |
|---|---:|---:|---:|
| `68989.ari` | 17.013 | 14.191 | -16.6% |
| `85782.ari` | 39.545 | 40.248 | +1.8% |
| `29415.ari` | 29.424 | 30.688 | +4.3% |

The large campaign regressions did not reproduce at comparable magnitudes.
Small differences remain; this is not a claim that every root becomes faster.
