---
type: Reconciliation Report
title: "Frozen checker branch reconciliation"
status: stable
---
# Frozen checker branch reconciliation

The audit compares primary `8a3ccdd2cc047e07dda39982c5ccd178e766d750` with
AAECC `40ff1810d06b510ed4802cb52ea70c2b2e15dbf4`, raw-superiority
`321f08db5a548f0cd7478250a37b866e6f917262` and the frozen AAECC dirty snapshot.
[Per-file source identities](branch-reconciliation-20261028.json) record the
comparison. No checker source, generated checking logic or executable changes
are required by these snapshots. This is a source reconciliation audit, not a
new Isabelle build or a new frontier-validation claim.

The AAECC innermost theorem is byte-identical on primary. The dirty snapshot's
QDP-to-SRS theory is also byte-identical (SHA-256
`9ee7daf566d98cb863cdc7a48f70e483c1e2a90caa0d2c49d66fc23372682d9f`).
Its parser tag, proof constructor, assumption propagation, side-condition checks,
soundness clause, CSR induction cases and session entry are already integrated.
The remaining RFC dirty changes only alter whitespace. Old generated exports
are not copied over the current exports.

The raw-superiority ADP adapter, argument filter, compound order checker and
compound reduction-pair theory are byte-identical on primary. The generic graph
implementation moved from `Relative_ADP/Checker` to
`Relative_ADP/Semantics/Dependency_Graph`: executable definitions are explicit
functions, with estimator soundness kept in the locale. Root-graph interpretation
and tests use that integrated implementation; tests also cover the guarded case.
The RFC checker differs by the `raw_isOK_unit` to `rfc_isOK_unit` lemma rename.
Full-to-outermost certification is integrated in `RFC_Absolute_Cert`.

The standalone raw campaign executable, sessions and retry-after-rejection
routing are obsolete. Current `Relative_ADP_Ceta` selects ordinary versus ADP
proof grammar structurally and `certify_proof_integrated` is exported through
the unified executable. These legacy wrappers are intentionally not restored.
Their commits remain historical evidence.

The executable remains SHA-256
`6422b02d3edef16005b4826b7568d7979ef2ad1311905e07a0428450988a802e`.
Ferrum migrations still require fresh preservation checks with this same binary,
and the final release gate remains open. See the
[binding integration contract](state-local-integration.md).
