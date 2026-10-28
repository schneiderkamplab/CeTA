---
type: Historical Report
---
# CeTA input-conversion performance (2026-10-26)

The shared Haskell input helper caches the exact generated singleton conversion
for all 128 ASCII characters. Non-ASCII characters still call the generated
decoder. File decoding, XML content, processor criteria and generated sources
remain unchanged. CPF, LP, conditional erasure and higher-order delegation use
the helper through their independent category adapters.

All category libraries and the thin dispatcher compile with `-O2`. GHC uses four
compilation jobs per category, with four concurrent category builds. Build cache
identities include shared helper hashes and package registration includes the
helper as a private module. No other worktree's binaries or heaps were changed.

## Measurements and rejected experiment

The initial character-cache build reduced the large relative-SRS Waldmann_26/14
check to 38.00–38.01 seconds (previously about 42), and 149713 to 111.79–113.47
seconds (previous measurements about 118–129). These are scoped outlier timings;
no whole-frontier speedup is inferred from them. Exact root identities, hashes,
verdicts and repeated timings are in `outliers.json`.

A direct lazy-ByteString decoder was also measured and discarded. It increased
Waldmann_26/14 to approximately 98 seconds; correcting its accidentally inferred
Integer array indices to Int still took 88–90 seconds on two repetitions.
Consequently the shipped implementation retains the original String input path.
The discarded experiment did preserve all 408 semantic rejections, but acceptance
alone was not sufficient to retain a performance regression.

This batch does not change the automata/RFC or size-change algorithms. Their
profiled tree/comparison costs remain candidates for an Isabelle-verified
implementation change; no generated code was edited to bypass that requirement.

Final-build scoped and full-frontier validation reports accompany this document.

## Final binary and focused verification

Source implementation commit: `8455e75`. Final executable SHA-256:
`e99680153bbd40cb6966b818d5a6c5e68ef2e07e907d4d1c7129ee2cbcd1d106`.
The receipt records every generated source, adapter and helper hash and all eight
`-O2` compilation commands. No Isabelle export changed in this batch.

Seven real outliers accepted twice on the final binary (`final-outliers.json`):
149713 110.47–110.99 s; Waldmann_26/14 38.04–38.58 s; LP minus2 1.94–1.96 s;
match-bounds 138477 9.75–9.80 s; Ex9Maps 8.45–8.79 s; RFC 259405 17.34–17.42 s;
HO h31 66.72–67.36 s. The outlier runner used three workers.

All 408 retained semantic negatives rejected with their expected diagnostics,
and dispatch/malformed-input checks passed. The exhaustive ASCII conversion test
and non-ASCII rejection comparisons passed against the generated decoder.

## Full certification refresh

All **5,412/5,412** frozen roots accepted in **344.25 seconds** with
32 workers and one check per root. Exact root sets, input/proof hashes, answers,
exit codes and verdicts match the preceding unified checker. This is certification
of frozen certificates, not a new Ferrum search. The preceding run took
357.96 seconds; a single campaign comparison does not establish a
controlled whole-frontier speedup. `frontier-final.json.gz` retains per-root timings.
