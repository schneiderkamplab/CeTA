# CPF 5: ITS and higher-order additions

CPF 5 preserves CPF 4, including every CPF 3 construct, and adds ITS and
higher-order rewriting extensions. CPF 4 is the first-order term/string
rewriting extension. LP, LP with cut and Prolog additions belong to
[CPF 6](CPF6.md), not CPF 5. Existing CPF 3 LTS features remain inherited at
every level; moving later ITS additions to CPF 5 removes no CPF 3 feature.

`cpf5.xsd` includes `lts5.xsd`, the first-order extension schemas, and
`cpf5-higher-order.xsd`. The higher-order schema is generated from the shared
native data grammar by `scripts/generate_cpf5_higher_order_schema.py`.
The grammar describes structured XML fields, not an opaque text payload.
`higherOrderInput` contains the source declarations and rules. The selected
proof constructor contains its certificate data. Delegation proofs embed their
first-order child under `firstOrderProof/trsTerminationProof`; new certificates
do not require a separately named child file.

The candidate Ferrum and CeTA implementations encode/decode these higher-order
forms under CPF 5 or inherited CPF 6, with version and claim checks. LeTA has a
direct XML reader and independent native criteria for all 20 higher-order root
forms. The three delegation forms retain gaps in first-order child decoding.
The precise constructor inventory is in the sibling LeTA repository at
`docs/cpf456-integration/higher-order-coverage.json`.

The historical 195-certificate compatibility replay and focused schema/mutation
gates are documented in the sibling LeTA `docs/state-local-integration.md`.
They do not establish a fresh full current strict/learned release replay.
ITS version-gate integration, complete native LeTA ITS coverage, explicit
legacy-only compatibility interfaces and the final full replay remain pending.

Run `tests/unified/check_cpf5_higher_order.py --checker PATH` for the focused
CeTA gate. Use the unified executable's `higher-order` category for direct
proofs and `higher-order-delegation` for embedded-child proofs. Schema validity,
proof acceptance and correspondence to the original input are separate checks.
