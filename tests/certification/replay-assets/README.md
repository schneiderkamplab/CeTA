# Frozen replay assets

These archives retain the complete audited search-only oracle, the producing
Ferrum source, and its private LP search dependencies. `manifest.json` pins their
hashes and the observed toolchain versions. The full oracle is deliberately
retained: trimming it to successful paths would discard native search choices
and make provenance harder to assess. It contains no exact witnesses or
composite proof recipes according to the recorded strict audit.

Regenerate the smoke corpus without reading any parent worktree or campaign:

```
python3 tools/consolidation/regenerate.py \
  --manifest tests/certification/harness-smoke/manifest.json \
  --assets tests/certification/replay-assets \
  --checker /absolute/path/to/ceta \
  --output target/packaged-regeneration
```

The command verifies assets, extracts private copies, audits the oracle again,
builds Ferrum with Cargo's locked offline dependency resolution, and regenerates
each original input. Install Rust 1.95.0 and populate the Cargo cache from the
archived `Cargo.lock` first. Python, cvc5 and Z3 must be available on `PATH`;
versions used here are recorded in the manifest. No binaries or dependency
caches in another thread's `target/` are needed. Platform toolchains are external
prerequisites, not claimed to be included in these archives.

Every regenerated proof must match its original input and pass the supplied
checker twice. Proof bytes can differ because search may find another valid
certificate. The result compares exact root names and answers, and retains
commands, hashes, logs and timings. This command checks replay and certification;
executable coverage remains a separate instrumented-suite gate.

For all 3,484 frozen roots, use `--manifest
tests/certification/replay-assets/full-replay.json`. The runner verifies and
extracts `all-inputs.tar.gz` privately and preserves the calibrated per-root
native search budgets. Use `--jobs 32` for parallel regeneration.

Add `--hpc-checker /absolute/path/to/instrumented-ceta --export-tix
/absolute/path/to/export-tix` to require instrumentation/production acceptance
agreement on every freshly regenerated proof and retain its coverage. Record
the checked source with `--checker-revision`. Coverage-denominator preservation
is still a separate gate; acceptance agreement alone does not establish it.
