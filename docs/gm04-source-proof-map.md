---
type: Specification
title: "GM04 source-proof replacement maps"
status: stable
---
# GM04 source-proof replacement maps

The standalone GM04 envelope keeps the original source replacement map and
signature as the definition of the transformed DP premise. An optional
`sourceProofReplacementMap`, immediately following `sourceReplacementMap`,
supplies the map used to check the independent source CSR proof. If omitted,
the source proof uses the original map, preserving existing certificates.

The checker requires both maps to agree on every symbol/arity in the fixed
source signature. Only auxiliary symbols outside that signature may differ.
For example, an improved CSR dependency-pair proof may freeze its fresh unary
wrapper without changing any source rewrite position or the GM04 schema.

`gm04_sig_csstep_cong` proves equality of the two rewrite relations restricted
to the fixed signature. The standalone checker checks the source proof under
its explicit map, transfers restricted termination through that equality, and
checks the unchanged generated schema and sole DP assumption. Extended source
signatures still require the existing global source-proof criterion. No global
termination claim follows from restricted termination alone.

The implementation is in `GM04_Standalone_DP_Checker.thy` and
`CPF_Proof_Parser.thy`. The isolated Isabelle build checked the theorem and regenerated the production
CPF library. The unified O2 executable has SHA-256
`362c56d7335a60bff89f84c19d54f437be5582fb2e125bb299514d99e0f94fac`.
All 21 source-map checks, 220 retained CSR checks and 164 focused Ferrum CSR tests
pass. Broader gates reject all 408 retained semantic negatives and pass twelve
dispatch checks plus 28 retained composition/mutation checks. The retained wrapper-sensitive fixture passes twice and rejects all five
semantic mutations. Omitting the optional map remains valid for source proofs
that do not require the auxiliary restriction, matching the preceding checker.
[Evidence](data/gm04-source-map-20261029.json) records both outcomes and the corrected
test expectation. Fresh unified full-frontier preservation remains pending.

Run the retained regression with `python3 tests/unified/check_gm04_source_map.py
--checker PATH --output DIRECTORY`. No generated checking logic was patched.


See the [historical envelope report](gm04-standalone-certification.md) and
[architecture integration contract](state-local-integration.md).
