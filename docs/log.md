# Update log

## 2026-11-08

- Completed SRS Relative concrete/serialized correspondence and strict partition binding.
  Six-category replay retains 4,013/4,013, including all 403 SRS Relative roots.
  Checker logic, executable and guidance are unchanged.
  [Verification receipt](data/srs-relative-review-20261108.json).

- Completed SRS Standard concrete/serialized correspondence and strict input binding.
  Five-category replay retains 3,610/3,610, including all 1,720 SRS Standard roots.
  Generated checker logic, unified CeTA and guidance are unchanged.
  [Verification receipt](data/srs-standard-review-20261108.json).

- Recorded the [three-category follow-up replay](../../ferrum/docs/reviewed-categories-replay-20261108.md):
  1,316/1,780 retained with the reviewed boundary; guidance compatibility remains open.

- Reviewed [Relative original-input certification](trs-relative-trust-boundary.md), including the
  signature-extension counterexample, explicit NO guard and partition checks.

- Added the concrete and serialized Innermost bridge with fixed nfs=false,
  no weak rules and certificate assumptions disabled. Concrete module contracts
  are discharged; both YES/NO conclusions use the canonical property.
  See the [review](trs-innermost-trust-boundary.md) for input binding, verification,
  certificate coverage limits and remaining inherited trust mechanisms.

- Added the [Standard integrated checker and trust-boundary review](trs-standard-trust-boundary.md),
  including runtime original-input enforcement in Ferrum.

- Reviewed [TPDB Standard conventions and parsing/dispatch](trs-standard-input-review.md);
  recorded remaining input-binding obligations and passing focused tests.

- Recorded [category bridge coverage and assumptions](category-assumptions-review.md),
  with an ordered review beginning at TRS Standard. Human review remains pending.

## 2026-11-07

- Collected the category theories into the [shared specification package](category-specifications.md)
  and added [TRS Innermost](trs-innermost-specification.md).
- Added the [ranked TRS Standard specification](trs-standard-specification.md),
  standalone examples, and separate semantic and checker bridge theories.
  Verification details are recorded on the specification page.

## 2026-11-05

- [Reconciled learned-only evidence](learned-only-validation-20261105.md): 6,570 certified inputs, all 6,565 required learned successes retained, two checks per acceptance by the same unified O2 binary. No checking logic or generated export changed during reconciliation. Main and the deferred independent two-checker release remain unchanged.

- Added an explicit absolute-RFC constructor to common recursive checking and
  its Isabelle soundness proof. The common checker/parser and legacy wrapper
  sessions pass; the integrated export and executable gates are pending.
  See [recursive residual checking](rfc-recursive-residuals.md).

## 2026-10-29

- Regenerated unified checker `0a3cca3` passes the complete 6,526-root / 15-category strict Ferrum frontier with repeated checks and original-input audits. [Release evidence](state-local-release-20261029.md).

- Proved agreement-based transport between the fixed GM04 source map and an explicit source-proof map. Regenerated the unified O2 checker; 21 source-map checks, 220 retained CSR checks and the retained mutation fixture pass. Full-frontier preservation remains pending. [Contract](gm04-source-proof-map.md).

- Proved signature-preserving CSR removal/GM composition, regenerated the production CPF export, and built the unified O2 checker. The 28 composition/mutation checks and 220 retained CSR checks pass; fresh runtime and full-frontier gates remain pending.

## 2026-10-28

- Audited frozen AAECC and raw-superiority branches against integrated main; retained source identities and obsolete-wrapper dispositions. Checker sources and executable remain unchanged.


- Added OKF indexes and typed metadata; preserved existing document bodies. Architecture requirements remain unverified until their gates pass.

- Pointed architecture links at the maintained Ferrum checkout for integration; checker implementation and executable are unchanged.

- Connected existing generated initial/return triple checkers to the unified LP adapter. Isolated O2 build and LP regression/negative checks pass; generated exports and installed main executable are unchanged.

- Integrated the existing verified finite-LP export into the isolated unified checker (`54a99ee`). Existing generated sources and other category libraries are unchanged. The new candidate passes 346 positive/81 negative checks, all 91 retained cut artifacts, and finite/dispatch regressions; main is unchanged.

- Scope correction: Prolog is deferred, including LeTA. The unfinished Prolog reconciliation is preserved separately at `19b6cbe` on `codex/deferred-prolog-reconciliation`; active work resumes on `codex/state-local-lp-cut` from the verified pre-Prolog snapshot. Only LP and LP with cut are in this migration scope. No Prolog candidate is promoted.

- 2026-11-08: Completed the checked CSR category review and full declared-map binding. Fresh four-category replay retains 1,890/1,890; [review and trust boundary](trs-context-sensitive-trust-boundary.md). No generated checker logic changed.

- 2026-11-08: Added TRS Outermost specification, examples, equivalence and concrete/serialized YES and direct-loop NO bridges. [Review](trs-outermost-trust-boundary.md); no generated checker changes.
