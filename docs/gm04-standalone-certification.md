---
type: Historical Report
---
# Independently certified GM04 residuals (2026-09-15)

`Proof_Checker/GM04_Standalone_DP_Checker.thy` connects an ordinary DP
obligation to an explicit, independently checked source CSR proof. It reuses
the verified GM04 schema theorem; no source termination assumption is trusted.
The source signature, replacement map, administrative roles, generated rule
schema and sole residual assumption are all checked. Extended signatures
require a global source proof. All other DP proof steps use the existing
ordinary checker, with their actual P/R/Q and minimality context.

`gm04StandaloneDpProof` is a top-level proof envelope. The corresponding
`gm04StandaloneTrsProof` envelope allows the same connection below ordinary
TRS transformations. It requires exactly one unconditional DP assumption,
checks that DP obligation using the source CSR certificate, then checks the
unchanged TRS proof. This does not enable unchecked assumptions globally.

Production integration is in `Proof_Checker.thy`, `CPF_Proof_Parser.thy` and
the regenerated Haskell modules. The production executable SHA256 is
`64597fcb0a8c1c09af1de0816283c66f474783df3010fc3e60ca30731f5090b7`.

Verification:

- `Proof_Checker` passed with eight threads in the isolated
  `target/isabelle-user-gm04-standalone-20260915` home. Existing dependency
  heaps were reused; the final parent heap is retained for further checks.
- The export-only child imports production `Code_CSR_Production` and adds no
  theorem or checker definition. Haskell export took 265 seconds; `make
  haskell` passed. Its production binary is identical to the isolated binary.
- All 152 residual audit proofs and all 1,759 retained root proofs passed
  production CeTA twice. The residual suite previously had ten remaining
  integration/reconstruction gaps at its last committed checkpoint.
- Both standalone-DP and nested-TRS positives pass. Mutations that collide
  administrative roles, remove the source proof, lose Q/normal-form conditions,
  or change the replacement map are rejected twice.

Build logs are `target/gm04-standalone-production-build-v3-20260915.log`,
`target/gm04-standalone-export-v1-20260915.log`, and
`target/gm04-standalone-production-make-20260915.log`. Ferrum's audit directory
`../ferrum-aaecc/target/residual-state-audit-20260915/` contains
`smoke-checks-v26-production.jsonl`, `gm04-production-root-rechecks-v1.jsonl`,
and `gm04-bridge-boundary-tests-production-v2/results.jsonl`.

No `sorry`, `quick_and_dirty`, axiomatization, or example-specific theorem was
introduced. Unrelated ROOT/outermost development changes were not included.
