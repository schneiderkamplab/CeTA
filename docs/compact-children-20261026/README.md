---
type: Historical Report
---
# Compact delegation children

All 36 retained first-order child certificates were compacted using the Ferrum
`cert::compact::layout_ranges` implementation. Only raw XML whitespace text in
element-only containers is removed. Leaf values (including whitespace-only
values), mixed content, entities, CDATA and inherited `xml:space="preserve"`
remain intact. Namespace normalization and proof obligations are unchanged.

Total size: 153,571,088 -> 32,720,721 bytes. For h31:
84,519,208 -> 13,756,001 bytes. The earlier regex estimate was smaller because
it also removed whitespace-only leaf text; this implementation preserves it.

`tests/unified/compact-children.tar.gz` contains the compact copies, and its
manifest maps original child hashes to compact hashes. Original archive and
provenance remain unchanged. The unified frontier runner uses compact children
by default and records both hashes. The production benchmark preparation in
CeTA-Lean also selects these compact copies.

All 36 source-bound roots certified twice with the unchanged CeTA executable
SHA-256 e99680153bbd40cb6966b818d5a6c5e68ef2e07e907d4d1c7129ee2cbcd1d106
at four workers. A further scoped run through the updated frontier runner
accepted all 36. No full-frontier replay was needed for this artifact-only change.

h31 native checks took 68.67 and 67.72 seconds (67.90 in the runner integration
check). This does not materially improve its previous 67-second native check.
Preparation in the scoped runner took 0.030 seconds, but concurrency and cache
conditions differ from the earlier 32-worker run, so that is not a controlled
preparation speedup estimate.

The Ferrum exporter fix is isolated in `ferrum-compact-certificates`, branch
`codex/compact-child-certificates-20261026`. It removes layout in the same export
pass as namespace normalization. The parent Ferrum source, production binary,
oracles and historical certificates were not changed. CeTA's executable and
Isabelle theory did not change; only its retained artifacts and runner changed.
