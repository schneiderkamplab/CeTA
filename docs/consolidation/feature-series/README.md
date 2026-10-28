---
type: Historical Report
---
This series contains the complete consolidation delta through `ecb7c83`, split
into 26 feature commits on branch `consolidated-features-20261018`. Applying
every patch to pinned main `e52c7ce` reproduces
the exact target Git tree, including generated code, test corpora, tools, and
verification evidence. Each intermediate application is checked against its
recorded tree hash in `manifest.json`.

The base already contains pre-consolidation development. These patches are not a
standalone upstream-ready series against downloaded CeTA 3.9 (`8e6e5f9`). The
inherited prerequisites require their own semantic decomposition and build
validation; the deferred outline below records that separate work.

The earlier five proof-only drafts in `../upstream-proof-series/` are superseded
by this complete consolidation series. The `consolidated` branch retains its
original history; reconstruction neither rewrites that branch nor touches the
development worktree. Synthetic commit identities and parents are recorded in
the manifest, and each patch includes the corresponding commit metadata.

The series branch shares the existing Git objects, avoiding a duplicate 344 MB
corpus patch in the working tree. Inspect it with `git log
e52c7ce..consolidated-features-20261018`. To export the complete patch set, run:

```sh
git format-patch --no-signature --full-index --binary -o /path/to/series e52c7ce..consolidated-features-20261018
```

Apply the exported files in order with `git am` in a separate checkout of the
pinned base. The manifest records hashes of the original verified export, made
with `git format-patch --stdout --no-signature --full-index --binary -1 COMMIT`
for each recorded commit. Whole-range export adds subject numbering, so its
patch bytes differ while the commit changes remain the same.
Regenerate Haskell from the theories when checking an intermediate source patch:
committed generated output is refreshed in the dedicated export patch near the
end. The final evidence patch introduces no production theories.

Build receipts target each feature's affected sessions. The QDP feature adds
one ordinary DP constructor and therefore carries both corresponding CSR
exhaustiveness-proof cases. These cases must neither precede the constructor
nor be deferred to a later integration patch.

Every feature now has a passing affected-session build or an explicit
evidence-only result. Build receipts, source hashes, timings, and the superseded
ordering failures are archived in `build-evidence.tar.gz`. The final export from
the series build is byte-identical to the committed integrated Haskell module. The final integration's
formal, certificate, negative-test, coverage, and provenance results are in
`../frontier-20261018/assessment.md` and the promotion extension’s
`../promotion-20261018/verification.json`, `campaign-comparison.json`, and
`criterion-coverage.json`. All 4,177 frozen proof/input identities certify.
This is certificate rechecking, not fresh Ferrum generation; the unavailable
SRS225 inventory remains outside the frozen set.

The deferred upstream prerequisite outline is:

1. Reconstruct the imported CeTA/IsaFoR and AFP session/toolchain prerequisites
   against the downloaded 3.9 source, preserving their original authorship.
2. Separate CSR/CSDP semantics, replacement-map representations, minimal and
   nonminimal criteria, usable-rule obligations, and executable implementations.
   Retain genuinely different criteria rather than merging names.
3. Separate the innermost/MU-TERM, guarded-measure, semantic-labeling, subterm,
   automaton, and transformation criteria already present in the pinned main.
4. Separate inherited relative-ADP semantics and processors, RFC/match bounds,
   and outermost-RZ semantics from their parser/export integration.
5. Reconcile the imported main histories and development tips by their pinned
   snapshots. Then rebase the consolidation features on those verified
   prerequisites, regenerate exports, and rerun the full certification gates.

No pre-consolidation feature is claimed to be newly implemented or independently
validated by these 25 patches merely because it is reachable from their base.
