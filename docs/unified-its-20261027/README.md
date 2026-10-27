# Unified checker including ITS, 2026-10-27

The previous unified checker was present on `consolidated` but had not been
merged into `main`. The ITS campaign incorrectly used separate checker binaries.
Merge `ef8d86480ee4b33c91dd8357947d8624fe727853` brings the complete consolidated
history (through `ca521b7d9448d1945c14f04ca3c3eb8c7f9c855a`) into `main`.
Commit `303a0368a2bcb0fa118e77eb42076ed5a7b25a4a` adds ITS to the existing unified
architecture. No subprocess checker is launched; each category is a private GHC
library in one native executable.

`make ceta` includes eight dispatch categories: CPF, cycle, conditional,
conditional erasure, LP, higher-order, higher-order delegation, and ITS. The ITS
adapter invokes the Isabelle-generated `check_its4_string` and prints `CERTIFIED`
only on success. Use `ceta --category its proof.cpf.xml`. Other category flags and
verdict text remain unchanged. Rejection never falls back to another category.

The merged source tree passed a fresh `ITS_Ext` Isabelle build and export.
Its generated Haskell snapshot is archived unchanged in
`tests/unified/exports/its.tar.gz`; source/archive hashes are recorded in
`scripts/unified-exports.json`. The seven previously verified category snapshots
are retained. All eight libraries and the dispatcher were compiled with `-O2`.
The verified executable SHA-256 is:

`6422b02d3edef16005b4826b7568d7979ef2ad1311905e07a0428450988a802e`.

The executable passed **5,412/5,412 protected roots**, with two certifications per
root, and **408/408 semantic negatives** with their expected rejection diagnostics.
The protected run took 500.31 seconds at 32 workers. This is certificate
revalidation, not a new search campaign or a controlled performance comparison.
All **1,114 ITS roots** also passed fresh native strict guidance replay, source
and CPF-schema audits, two checks each, receipt/guidance equality, and checkpoint
reconstruction with the same executable. Total: **6,526 roots in 15 benchmark
categories, 13,052 successful checker invocations**. No baseline roots were lost.
Ferrum's `scripts/audit_unified_release.py` rejects mixed checker hashes, missing
roots, changed source identities, and missing second checks.

`frontier.json.gz`, `negatives.json.gz`, `dispatch.json`, `build.json`, and
`committed-source-attestation.json` preserve the exact evidence. ITS and combined
release evidence is in Ferrum's `docs/unified-checker-20261027-validation.json`
and `docs/its-unified-20261027-validation.json`. The test suite includes 25 native
ITS tests, 37 certificate tests, three recurrent tests, three conditional
property-separation tests, and unified routing/catalog tests. A stale separate
recurrent-checker environment variable in the test harness was corrected and
that suite rerun; the original failed harness log is retained.

The installed `CeTA/ceta` is an exact copy of the immutable, validated executable.
A subsequent `make ceta` relink produced a different byte hash; that build is
retained separately and is not the production pin. `installation.json` records
both identities. Do not replace a production binary after validation or claim
that a same-source rebuild has the same byte identity without checking it.

Reproduction uses `make ceta`, then `tests/unified/check_dispatch.py`,
`tests/unified/check_frontier.py --passes 2` with the retained 5,412-root archive,
and `tests/unified/check_negatives.py`. Freeze the resulting binary before
starting checks. All ITS checks must use that same frozen binary with explicit
`--category its` dispatch. Standalone category builds remain development tools,
not production checker selections.
