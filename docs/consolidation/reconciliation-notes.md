# Reconciliation decisions to verify after the baseline

These notes describe source-inspected changes, not completed proof or export
verification. No semantic simplification is justified merely by the runtime
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
