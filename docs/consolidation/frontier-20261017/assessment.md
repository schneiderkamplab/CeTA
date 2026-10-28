---
type: Historical Report
---
# Frontier integration snapshot

The user explicitly reopened relative ADP and outermost-RZ for integration.
The snapshot in `sources.tar.gz` records uncommitted frontier sources, with base
commits and individual file hashes in `manifest.json`. These sources are inputs
to verification, not evidence of a previously verified frontier build. Later
changes in the parent worktrees are outside this snapshot.

## Selected architecture

* RFC `Split` recurses through the existing RFC checker for both children. It
  uses the existing `split_tt` semantics and soundness lemma; there is no second
  split criterion or separate root/subproblem engine.
* Relative ADP compound orders require strict monotonicity at both `Com2`
  arguments. Ordinary symbols retain the weak context closure required by the
  reduction triple. One general criterion supports the executable checker;
  the former fully monotone finite theorem remains a compatibility corollary.
  This is a genuine weakening of an unnecessarily strong applicability condition,
  not identification of different ADP problem semantics.
* The outermost bridge checks full termination with the existing RFC/ordinary
  engine and derives outermost termination by relation inclusion. It introduces
  no RZ processor, alternate residual semantics, or copy of the full checker.
* The existing relative-ADP integrated CLI parses each certificate once,
  selects the proof parser by the first child tag of the parsed proof node,
  and dispatches to the shared ordinary/RFC or ADP checker. No preliminary whole-document scan is
  performed. Failure in either dispatch branch never grants proof credit.
  `ceta` retains its RFC/ordinary entry point; `ceta-relative-adp` is the integrated
  entry point, and `ceta-ordinary` retains the original ordinary interface.

The integrated parser explicitly uses `lab.Sharp`: importing the production RFC
layer also brings a different `Sharp` constructor into scope. Shared imports are
placed in the `Relative_ADP_Integration_Base` parent session so parser changes
reuse a checked heap instead of rechecking all imported production theories.

## Excluded sources

* The 844-line duplicate `Relative_ADP_Checker_Adapter_Test` is not imported.
  Tests import the production adapter.
* Campaign-specific console exports, absolute output paths, and parallel
  `Raw_Campaign_*` checker wrappers are not imported.
* The old verification worktree's broader forbidden-pattern input bridge is
  archived for comparison. Only the requested outermost capability is added here.
* No new RZ-specific implementation was found. The incomplete, untracked
  `Outermost_CDP_Core` generation criterion is not promoted to production.

## Coverage and provenance boundaries

The frozen original compact denominator remains unchanged. New executable code
requires new instrumentation and an explicit coverage transition, rather than
reuse of the old binary-identity argument.

The supplemental frontier manifest freezes 48 Ferrum-produced proofs: 26 relative
ADP, 19 outermost RZ transformation, and three RFC proofs below `Split`. All 48
match their original inputs, including relative strict/weak partitions and
outermost strategy. Their generation source/build provenance is incomplete, so
these are supplemental acceptance/regression evidence, **not** additions to the
strict witness-free oracle-only positive suite. The source command and original
artifact record are retained. The old binaries accept all 19 RZ and three RFC
proofs; only the 26 ADP proofs distinguish the new capability in this corpus.
The outermost full-termination bridge has a separately labeled derived strategy
fixture; these RZ proofs do not cover that new branch. No synthetic proof is described as a real replay.

Two separately labeled derived fixtures exercise the new full-to-outermost
bridge and absolute-RFC recursion below `Split`; the old checker rejects both.
Their source proofs come from the genuine compact suite, but the adaptations
are synthetic and do not contribute genuine replay coverage.

The ADP order theory includes positive and negative executable tests. Additional
well-formed CPF mutations remove either compound argument from polynomial
interpretations and require the compound-monotonicity diagnostic; crashes,
timeouts and parse errors are not accepted as semantic rejection. The RZ
proofs also receive marker-freshness mutations, and nested RFC proofs receive
mutations that replace a nonempty selected component with an empty-rules proof.

Verification results and failed preliminary attempts are recorded separately. The existing 3,484-root corpus is rechecked, not described as a
fresh Ferrum replay or as exhaustive coverage of the moving current frontier.

## Reproducing the checks

`tools/consolidation/build_verified.py --revision REV --isabelle ISABELLE
--ghc GHC --output BUILD --relative-hpc` builds the committed source, all required
sessions/exports, three production entry points and both instrumented checkers.
It uses private build directories and the repository's frozen dependency assets.

Run `frontier_suite.py` with the supplemental `manifest.json`, the integrated
production checker and its HPC counterpart. Run it separately with
`bridge-fixtures.json` and the RFC production/HPC checkers. The separation keeps
real frontier artifacts and derived fixtures distinct. Supply a fresh `--output`
directory each time. The runner also checks separate-input invocation and unknown
proof-node rejection; those parser tests are not counted as semantic negatives.

`recheck_packaged.py` rechecks the frozen full replay with two production checks,
HPC agreement, exact root/input identities and an optional `--additional-checker`
for the integrated entry point. It explicitly records that this is certificate
rechecking, not fresh Ferrum generation. It stops launching new checker processes
while total minus available memory is above 2 TiB.


## Large-certificate dispatch regression

The compact suite did not expose whole-document retention in the integrated
entry point. Full-corpus checks exposed high memory use and timeouts on large
SRS certificates. Controlled measurement showed that the previous ADP-first
integrated checker also retained the input: the 2.64 GB reference certificate
took 397.6 seconds and approximately 204 GiB peak RSS. The default checker
certified the same input in about 108 seconds. The final single-parse integrated
checker certifies it in 102.1 seconds with 17.0 GiB peak RSS. These are individual
controlled large-certificate measurements, not campaign-wide memory peaks.

The final integration parses the document once. It selects the existing proof
parser by the first child tag of the parsed proof node and dispatches on the
resulting sum type. Both selected parsers validate their complete proof; unknown
nodes remain errors. The new dispatch soundness lemma uses the existing
ordinary/RFC and ADP soundness theorems. There is no whole-document fallback or
preliminary scan. The evidence retains initial failed attempts, controlled
measurements, and checks of the corrected checker across the full frozen corpus.

## Verified outcome

[verification.json](verification.json) records the final gates and binary hashes;
[evidence-validation.json](evidence-validation.json) verifies every archived
receipt and the 3,849 production source files against the isolated build.

* All affected Isabelle layers and all five integration/export targets pass.
* Both production entry points pass 208 compact positives and 408 semantic
  negatives. Default production/HPC checks preserve all 45,733 retained
  obligations; the previous 20 retirements are unchanged.
* All 3,484 frozen roots pass twice with the default checker, agree with HPC,
  and pass with the corrected integrated checker. Exact root/input identities
  and required coverage are preserved.
* The 48 supplemental proofs pass production/HPC agreement and 74 semantic
  mutations. Both derived fixtures also pass through default and integrated
  entry points. New parser and dispatch entries execute on all 50 integrated
  fixtures; no unknown proof nodes were found.
* The corrected compact suite has no slowdown candidates. The large-certificate
  comparison above verifies the memory improvement missed by compact coverage.

This completes integration of the frozen snapshot. It does not claim a fresh
Ferrum regeneration or exhaustive certification of a later, moving frontier.
The provenance and genuine-coverage gaps above remain explicit.
