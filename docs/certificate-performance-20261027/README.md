---
type: Historical Report
---
# XML/CPF decoding, batch rule operations, and certificate term sharing

The four parser refinements and both additional optimizations are implemented
in the isolated `consolidated` worktree. Existing production binaries and the
parent CeTA/Ferrum worktrees remain unchanged.

## Verified checker changes

`thys/Certificate_Performance/XML_Performance.thy` proves:

- Fixed tag strings can be prepared at parser construction/call sites.
- Failed tag alternatives can advance directly without constructing an
  intermediate mismatch result. Adjacent pairs of alternatives dispatch on the
  XML node once, preserving callback fallback, fatal errors, and expected-tag
  order. This is pairwise dispatch, not a global tag-numbering scheme.
- Text without `&` can retain its original representation.
- Text normalization can be fused into recursive XML construction instead of
  mapping a second complete XML tree. The entire parser result, including
  errors, equals the original implementation. A complete XML tree is still
  constructed; this is not a streaming CPF decoder.

`Rule_Bucket_Performance.thy` proves batch insertion with an auxiliary membership
index and batch deletion by filtering buckets once. Both preserve exact original
values, bucket list order, and RBT structure/colors. Deletion replays the original
key-touch sequence because even an existing-key insertion can rebalance the tree.
No new semantic assumption is introduced.

`Certificate_Performance.thy` rejects proof admissions and any oracle dependency
in the refinement theorems. All generated Haskell comes from Isabelle exports;
none is patched manually. CPF, conditional erasure, higher-order delegation, and
all six LP XML modules were regenerated. Cycle, conditional nontermination, and
non-delegating higher-order entry points do not contain the changed parser or
bucket operations. All category libraries and the main executable use `-O2`.

## Certificate sharing

`tools/cpf-share` is a standalone production export pass that uses existing CPF
term lookup tables. It shares only identical syntax and emits earlier bindings
before references. Relative-ADP documents, other XML formats, existing tables/references, namespaces,
and proofs that would not shrink remain unchanged. Non-XML artifacts are copied.
This changes certificate representation, not proof search or checker acceptance.

Every changed proof was independently audited by streaming XML expansion hashes
of the complete certificate, including input and metadata. Among 5,283 unique
proofs for 5,412 roots, 3,436 shrank and 1,847 stayed byte-for-byte unchanged.
Uncompressed primary certificates fell from 18,413,345,128 to 2,658,408,051 bytes.
The ZIP archive fell from about 438 MiB to 173.35 MiB. All 36 delegation children
also passed the expansion audit; none shrank further.

The shared archive is `target/shared-frontier-compatible-20261027/frontier-5412-shared.zip`,
SHA-256 `f588c560df02fc286440327e1955264296e7ecbd423f5181515ffe7fac22c1e0`.
The original and compact archives are retained. LeTA continues to use the
explicit-term compact corpus: its Python adapter does not support nonempty CPF
lookup tables. No oracle or production registry is replaced by this export pass.

## Reproduction and provenance

Native build from committed generated snapshots:

```
python3 scripts/build_unified_checker.py --output target/unified-performance --jobs 4
```

The archived export scripts and wrappers record exact Isabelle commands, source
paths, constants, and timing receipts. They reuse the task's private Isabelle
`usable_membership_20261026` heap copies, never shared writable heaps. The frozen
Proof_Checker source and LP source archive/revision are documented in
`../usable-membership-20261026/README.md`; `LP_Cut_NO_Generated` additionally
reproduces its previous export byte-for-byte before applying the refinements.
`theory-sources.json` pins every refinement and session wrapper.

To reproduce sharing, build `tools/cpf-share` using its Cargo lockfile, then:

```
python3 tools/consolidation/share_frontier.py \
  --manifest target/compact-frontier-20261026/manifest.json.gz \
  --archive target/compact-frontier-20261026/frontier-5412-compact.zip \
  --compactor target/cpf-share-build/release/cpf-share \
  --output target/shared-frontier-new --workers 16
```

The process pool avoids Python's thread serialization during the independent
XML audits. Receipts are resumable only when output and binary hashes match.
The final fresh export and expansion-audit pass took 138.20 seconds with 16
worker processes. Earlier export attempts and their diagnosis are retained.

## Validation and performance

Final certification results and controlled timing comparisons are recorded
alongside this report. Timings are certification-only; no Ferrum proof search
was rerun. The comparison keeps exact root identities, original-input hashes,
answers, and original proof hashes fixed.

### Rejected intermediate export

The first candidate was not released. Its CPF export accidentally used
`Code_Target.produce_code ... true`, making every generated helper public,
instead of preserving production's narrow exported interface. On the *identical*
644 KiB `SRS_Relative/ICFP_2010_relative/128056.ari` certificate, production took
3.94 s and allocated 33.31 GB; both the parser-only and combined all-public
candidates took 71.8–73.8 s and allocated about 355 GB. Sharing did not alter this
certificate and was ruled out. The initial full run was stopped, and its partial
results are retained under `diagnosis/`; they are not reported as a completed
frontier validation.

CPF is regenerated with `all_public=false`, matching the production export
boundary and the committed Isabelle session's `export_code` command. The native
builder now checks the CPF public API against the manifest before compiling,
preventing accidental exposure of internal helpers. Parser-only timings from the
all-public candidate are confounded by that export change and do not isolate the
parser refinements' performance.

### Relative-ADP representation compatibility

The corrected native checker completed the full 5,412-root, 32-worker run with
5,391 accepted and 21 unsupported shared relative certificates. All 21 contained
`relativeAdpTerminationProof`. The integration's `xml2relative_adp_root` path
uses fresh maps (see `Relative_ADP/Integration/Relative_ADP_Ceta.thy`, including
`Mapping.empty` calls and `integrated_proof_parser`); it does not uniformly pass
the document's term lookup table into proof fragments.

The exporter now retains any document containing that processor form verbatim.
It does not weaken the checker or ignore a failed certificate. This changed 23
outputs: the 21 unsupported cases and two previously accepted documents. All 23
were rechecked with 32 workers and accepted. The other 5,389 results were reused
only after exact proof hashes matched the final archive. `frontier.json.gz`
records the full run plus these scoped rechecks, the parent report hashes, and
all 5,412 final successes. This is not presented as a second fresh full run.

Final native binary SHA-256:
`dc31c2c32fd7c1bb000c08e7d8d492330307cbceeb74a4ed54de48ff1e101cd1`.
The final checker passed all 96 old/new parser-result comparisons, all 408
retained semantic negatives with expected diagnostics, and the dispatcher tests.

### Measured results

Controlled `SRS_Standard/ICFP_2010/161533.ari` runs alternate old/new order;
figures below are means of two runs, with the same certificate bytes in each
column. All checks accepted.

| Checker | Explicit CPF | Shared CPF |
|---|---:|---:|
| Previous production | 84.08 s | 26.19 s |
| Refined checker | 73.32 s | 18.41 s |

Thus the checker changes reduce time by 12.8% on the explicit form and 29.7% on
the shared form. Combining sharing and checker changes gives a 4.57× speedup
against production's explicit form. Allocations fall from 214.58 GB to 26.20 GB
in that combined comparison; maximum live heap falls from 9.01 GB to 0.79 GB.
On identical representations, maximum live heap rose about 7%, despite lower
allocation. The changes do not improve every memory metric.

The complete frontier's recorded native-time sum falls from 5,256.86 s to
4,103.74 s (21.9% lower). Mean checking time falls from 0.9713 s to 0.7583 s;
p95 from 4.0684 s to 3.8485 s; p99 from 19.8065 s to 17.4011 s; maximum from
86.6826 s to 53.6652 s. Median rises from 0.1185 s to 0.1315 s. These concurrent
measurements are not isolated microbenchmarks.

End-to-end wall time is **not** improved in this measurement: the full run plus
scoped compatibility rechecks totals 347.69 s versus 331.73 s previously.
Aggregate preparation time increased from 1,271.94 s to 1,682.75 s. Do not equate
lower total checker time with a faster whole harness run or attribute all
variation to the checker. Per-root raw timings are in `per-root-times.csv`.

### Slowdown investigation

All 238 roots showing both >20% and >0.2 s increases in the concurrent run were
repeated three times with paired old/new commands, using 16 workers and already
prepared files. None retained both thresholds. The 27 remaining >20% ratios
(all very short checks) were repeated serially. Two still exceeded 20%, so both
received 15 serial repetitions distinguishing checker changes from sharing.

`SRS_Standard/Wenzel_16/aabbaaaaa-aaaaaaabbaabb.srs.ari` is a real small-form
tradeoff: median 12.19 ms before, 12.73 ms after with explicit terms, and 23.02 ms
after with sharing. Its proof shrinks from 19,217 to 10,802 bytes. The extra
lookup-table decoding costs about 10 ms here. The other case,
`TRS_Standard/AProVE_08/id_inc.ari`, settled at 12.03/12.91/12.67 ms respectively;
its earlier large percentage difference did not persist. Sharing is an optional
export pass optimizing storage and large repeated certificates, not a promise
of lower latency for every tiny proof. The checker still accepts explicit forms.

The final exporter was rebuilt from the retained source and reproduced all
5,283 outputs byte-for-byte (`sharing-reproduction.json`). The Rust exporter has
five passing targeted tests; the independent expansion auditor has two passing
positive/negative test groups. No parent checker, oracle, worktree, or production
default was replaced.
