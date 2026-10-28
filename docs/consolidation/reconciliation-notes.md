---
type: Historical Report
---
# Reconciliation and export decisions

The reconciled source has passed all four Isabelle integration/export targets.
Reconciliation compact/corpus gates pass, and the export cleanup has passed
its focused/compact gates. Fresh final replay is recorded separately. No semantic simplification is justified merely by the runtime
coverage observed so far.

## Preserve the general innermost GM04 adapter

Pinned CeTA main `e52c7ce` accepts an ordinary child proof for its actual input
`T`, then discharges precisely the certified GM04 residual assumptions. In
pinned CeTA-CSR main `17dbee4`, the innermost constructor additionally computes
the complete transformed rules `C` and checks variants in both directions
between `T` and `C`.

The innermost case of `check_gm04_complete_transformation_proof_sound` does not
use those two extra checks. Retain the general CeTA-main behavior when merging
the new full-rewriting constructor and nontermination functionality. The full
constructor has a different theorem argument and must retain its own complete
transformation checks. This is preservation of two existing capabilities, not
an identification of full and innermost criteria.

The two pinned `CSR_Conservative_Checker.thy` blobs are identical. Their history
does not require inventing a competing implementation. The parser changes are
mostly additions, but the direct-CSR alternative moves after specialized
alternatives; verify existing accepted forms and unknown-node rejection when
reconciling that order.

## Share Haskell export configuration

`Code/Code_Haskell.thy` and `Proof_Checker/Code_CSR_Production.thy` contain the
same module-name configuration. The latter omits the actual `export_code`
command. Factor that shared configuration into one imported theory, retaining
small compatibility entry points for both existing theory names.

The `Code` session currently inherits `IsaFoR_3`, which reloads checker theories
already present in the separate production `Proof_Checker` session. Assess
making `Code` inherit `Proof_Checker` directly. Preserve the legacy IsaFoR
aggregate sessions for callers that request them; they need not be on the
production export path. Verify all ordinary, RFC and relative-ADP exports and
regenerate Haskell from their checked theories.

## Incremental build isolation

The baseline build uses
`target/consolidation-build/checker-source` as its private source root. After
that build finishes, update this same private root from each explicit
consolidated source snapshot. Keep the snapshot commit/archive and exports for
each milestone. Use a new Isabelle identifier and output directory seeded by
private copies of the preceding verified heaps. Keeping the source path stable
allows unchanged dependencies to remain compatible; creating a new source
path for every batch would needlessly invalidate them again.

Never update this private root while a build is reading it. Never change an
existing parent worktree, production binary or shared heap. The baseline
environment and interruption receipts remain under the isolated build tree.

## Prepared reconciliation

The isolated merge was committed as `a485775` after all reconciliation gates passed. Compared with pinned CSR main, the entire
`thys`, `dev` and `src` source surface differs only by removal of the three
innermost GM04 lines computing `C` and checking both variants directions.
The parser, standalone bridges, full GM04 and nontermination additions were
reviewed as additions to CeTA main. The full constructor retains its guards.
No newly added proof admissions were found in the 20 changed theories.

The immutable prepared source tree is
`ab4a952a905c7bbd6ac1ebb92e5340b67378303c`; it is the immutable source snapshot tested before the merge commit. See `gm04-criterion-coverage.json`
for 13 innermost and 11 full-transformation selected roots, paired freshness
negatives and remaining side-condition gaps.

The two GM04 contexts remain different: the general innermost adapter preserves
its actual Q context, whereas the full constructor requires Q to be empty.
The full constructor's legacy `joins` payload is parsed and retained for CPF
compatibility, but is not used by its checker branch or soundness proof as a
confluence premise. It must not be counted as a separate checked criterion.

Keep `gm04_finite_residual_variants` and `gm04_finite_residual_rule_subset`
as distinct results. The former assumes finiteness at one fixed minimality
flag and rule equivalence. The latter assumes finiteness for every minimality
flag and permits target weak-rule subsets; it uses the former at `False`.
Replacing the former with the latter would strengthen its hypothesis. Also,
`gm04_rules_variant_subset S Rw` means that every rule in **Rw** has a variant
in **S**, despite the argument order. The accepted residual compares normal-form
sets for Q, not literal Q-list equality. These distinctions are now explicit in
the criterion inventory.
