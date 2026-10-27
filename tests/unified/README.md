# Unified CeTA executable

Build from the committed, hash-pinned Isabelle export snapshots:

```
make ceta
./ceta --list-categories
./ceta proof.cpf.xml
./ceta --category cycle cycle.certificate
./ceta --category conditional --ordinary conditional.certificate
./ceta --category conditional-erasure erasure.xml
./ceta --category lp lp-certificate.xml
./ceta --category its its-proof.cpf.xml
./ceta --category higher-order higher-order.certificate
./ceta --category higher-order-delegation higher-order.certificate child.cpf.xml
```

`cpf` is the default and preserves the integrated ordinary/relative/CSR/SRS,
AC/equational, RFC/match-bounds and other CPF processor paths. `conditional`
without `--ordinary` retains the existing operational conditional interpretation;
`--ordinary` explicitly selects ordinary rewrite-loop checking. Do not discard this
flag when translating an existing invocation. LP covers pure LP and LP with cut.
The higher-order adapter retains `--explain`. Verdict text and exit codes are
preserved from the category entry points.

`src/Haskell/Main_Unified.hs` only dispatches. Eight files under
`src/Haskell/Ceta/Category/` own the category-specific parsing and invocation.
No child checker processes are launched. A failed category never falls back to a
checker for another relation. Unknown categories and malformed invocations fail.

## Independent changes and build isolation

Each category is a private GHC package with its own unit identity, generated
modules, object directory and build receipt. Only its adapter is exposed. This
prevents two independently exported modules named `Arith`, for example, from
silently resolving to the wrong implementation. It does retain private copies of
common generated foundations across export boundaries; it does not introduce new
theorems or alternate proof criteria. Sharing those foundations requires compatible
Isabelle exports and can be a separate verified build improvement.

`build_unified_checker.py` hashes the generated source set, adapter, shared input helpers, compiler version,
and flags. Unchanged category archives are reused; a changed category recompiles
independently, then the small dispatcher is relinked. All compilation uses `-O2`,
including generated modules and the main layer. Fresh object directories prevent
reuse of historical `-O0` objects. Haskell runtime/system libraries remain the
compiler distribution's libraries. The default build has four concurrent category
builds, each using up to four GHC compilation jobs. It does not modify shared heaps or another worktree's artifacts.

The committed `exports/*.tar.gz` files are unchanged generated Haskell snapshots,
not hand-resolved generated-code merges. `scripts/unified-exports.json` records
all module hashes, compressed archive hashes and export origins. The default
build extracts and verifies them privately. An explicit `--exports DIRECTORY`
can supply the same verified files. A new category export requires an intentional
manifest/snapshot update following the affected Isabelle session's verification;
changing the source directory alone cannot silently change the build.

To update one category: build/export its Isabelle session privately, verify its
soundness/export target, replace that category's archive and hash manifest entry,
adapt its `Ceta.Category.*` module if needed, and run its positives and paired
negatives. Existing category files and objects need not be replaced. New categories
also need a dispatcher entry and integration tests. `make haskell` remains the
explicit legacy RFC-only build; `make ceta` is the unified production entry point.

## Snapshot scope

This integration covers all categories in the frozen 5,412-root production
frontier. It does not silently import later development work. Generated LP modules
match the v145 production receipt. Its handwritten driver changed after that
receipt and was not retained in its recorded commit; the LP adapter is explicitly
a new snapshot of that driver, tested against all frozen LP rows. Higher-order
call-expansion's driver was reconstructed from its recorded commit plus source diff
and checked against its recorded hash. The delegation driver was recovered from
commit `3ec50fc`. Conditional adapters retain the ordinary-mode distinction.

The export cache allows the executable to be reproduced without depending on
mutable paths in another thread's `target/`. This is a native integration build of
previously verified exports, not a claim to have rerun every Isabelle session in
this change. The source-of-truth theorems remain the Isabelle theories.

## Validation

`python tests/unified/check_dispatch.py PATH/TO/ceta` checks category listing,
malformed certificates, unknown categories and argument errors. These are dispatch
checks, not substitutes for semantic negative tests. Full-frontier and retained
semantic-negative results are recorded in `docs/unified-20261026/`.

The 36 higher-order child proofs are retained in `children.tar.gz`, with their
original hashes. The runner extracts and verifies them privately instead of
relying on the old production thread's child-proof paths. Its certificate/input
archive is the frozen frontier archive identified by the provenance hash.

## Input conversion

`Ceta.Input.Characters` caches the generated decoder's exact singleton result
for each ASCII character. It retains `readFile`, the original non-ASCII decoder
and every XML/parser obligation. There is no whitespace normalization or
certificate rewriting. Each category keeps its own generated character type.
Run `runghc -isrc/Haskell -itarget/unified-exports/cpf
tests/unified/Characters.hs` to compare all ASCII values and Unicode rejection
against the generated decoder. Performance measurements and final validation
are recorded in `docs/performance-next-20261026/`.

## Compact delegation children

The default frontier runner uses `compact-children.tar.gz`. Its manifest records
both original and compact hashes; `children.tar.gz` retains the original corpus.
Only element-only XML layout was removed; leaf values and explicit whitespace
preservation are retained. All 36 compact source-bound delegations passed twice.
See `docs/compact-children-20261026/` for sizes and timings.

## ITS integration (2026-10-27)

The `consolidated` history is merged into `main` at `ef8d864`. ITS is the eighth
dispatch category, backed by a fresh `ITS_Ext` Isabelle export from the merged
source tree. Its adapter calls only `check_its4_string`; it does not invoke the
standalone `ceta-its` binary. CPF3/CPF4 ITS termination, exact-state lassos,
recurrent regions/cycles and nonzero constant-divisor arithmetic share this path.
Generated modules are archived without edits. `make ceta` includes ITS by default.

Frontier validation accepts `--passes 2` for two checks per retained root with
one immutable binary. ITS guidance replay must use that identical executable
with `--category its`; standalone development binaries are not production pins.
