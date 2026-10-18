# Upstream patch-series extraction and remaining outline

Extraction has started: `upstream-proof-series/manifest.json` records five
proof-only draft patches against the pinned consolidated prerequisite `85b6876`,
with exact sequential apply verification. See `shared-checking.md` for scope and
verification limits. They are not yet a series ready to submit against CeTA 3.9.

The remaining feature reconstruction follows this dependency outline. The consolidated branch and frozen source snapshots remain the source
of truth. Do not replay entire development branches or merge into parent branches
as part of this task.

1. **Problem interfaces and assumptions.** Extract the retained QDP/CSR problem
   semantics and soundness interfaces before their executable users. Preserve
   minimality, Q-normal-form equivalence, strict/weak partitions and replacement
   maps. Keep the distinct minimal/nonminimal and full/innermost criteria.
2. **CSR and typed MU-TERM families.** Separate shared semantic foundations from
   executable checks, then add specialized usable-rule and unhiding criteria with
   their explicit premises. Historical alternatives require a proved replacement and caller accounting;
   matching benchmark outcomes do not justify deletion. The user authorized
   formal refactoring without genuine replay coverage. See
   `theorem-retirement.md` for the finite conservative coverage specialization
   and guarded endpoint/rank corollaries.
3. **GM04 and residual bridges.** Add schema, signature and freshness results,
   then full/innermost constructors and standalone/nested adapters. Preserve the
   general CeTA-main innermost child interface. The obsolete innermost complete-
   rule guards can be omitted because its soundness argument discharges the
   actual child's residual assumptions; full and nontermination guards remain.
   Keep fixed-minimality rule-equivalence and all-minimality weak-rule-subset
   lemmas distinct. Preserve Q by the actual normal-form obligation.
4. **Relative ADPs — reopened for integration.** Retain annotations, graph child counts, variable-reposition
   conditions and separate erasure/Com reduction-pair obligations. Build and
   export the integration target independently. The user subsequently authorized moving these theories into `thys/Relative_ADP`
   with formal and executable-equivalence verification. The retained hand-written
   fixture still does not qualify as a genuine witness-free replay.
5. **RFC, match bounds and rule strengthening.** Keep initial-language coverage,
   automaton closure, right-linearity and residual signature assumptions visible.
   Absolute and relative residual contracts stay distinct. Include their RFC
   export and genuine SRS evidence in reviewable increments.
6. **Outermost-RZ — reopened for integration.** Keep the committed RZ transformation and its cover/freshness
   conditions. The frozen 2026-10-17 snapshot adds 19 real supplemental positive RZ proofs and marker-freshness rejection tests; their generation provenance is insufficient for the genuine replay denominator. The user subsequently authorized
   extracting the transformation criterion from recursive checking, verified
   formally and by exact generated-code comparison. Four outermost nontermination
   replays remain insufficient evidence of the positive transformation path.
   Uncommitted CDP and alternate unhiding work is excluded.
7. **Compatibility integration.** Preserve CPF parser alternatives, explicit
   unsupported-node behavior, split-input CLI flags and assumption policy.
   Keep hand-written CLI adapters separate from generated modules.
8. **Session/export/build plumbing.** Factor duplicate Haskell configuration,
   retain compatibility theory names, route ordinary export through the verified
   production session, and use the standard Isabelle export mechanism for the
   relative checker. Produce separate binaries and object directories. Treat
   shared-heap isolation and all export targets as acceptance requirements.
9. **Generated artifacts and regression evidence.** Regenerate from the preceding
   verified theories. Include durable inputs, compressed real certificates,
   semantic negatives, oracle/source assets, exact replay comparisons and explicit
   coverage transitions. Split large archives according to the eventual upstream
   project's artifact policy without losing content-addressed provenance.

Each eventual patch should connect its theorem premises, executable guard,
parser form, genuine positive and intended semantic rejection. Runtime coverage
is not theorem coverage. Freeze the denominator for each milestone and explain
any retired obligation. The user has authorized starting draft extraction now. Promote the complete
feature series to upstream-ready only after its prerequisites are reconstructed,
its own integration builds pass, and the final replay gate is satisfied.


## Frontier snapshot integration, 2026-10-17

The user lifted the relative-ADP and outermost-RZ deferral. The next upstream
increments should separate these verified source changes:

1. Generalize the ADP compound-order criterion to strict monotonicity at both
   compound arguments; retain the fully monotone finite theorem as a corollary.
   Add its executable order guard and migrate the existing adapter.
2. Add recursive RFC `Split` checking using the existing problem operation and
   soundness theorem; avoid a parallel root/residual engine.
3. Derive outermost termination from full termination and route the certificate
   through the existing RFC/ordinary engine.
4. Parse certificates once and dispatch their parsed proof to the existing
   ordinary/RFC or ADP checker. Prove the shared dispatch soundness lemma, qualify
   the parser constructor, and factor shared imports into a parent session.
   Regenerate exports from these theories.
5. Include the frozen supplemental corpus, separately labeled derived fixtures,
   semantic rejection mutations, coverage transition and verification receipts.

See [the snapshot assessment](frontier-20261017/assessment.md). No new RZ
implementation was imported; the incomplete CDP criterion remains excluded.
The five earlier draft proof patches remain prerequisite-dependent drafts.
This outline does not claim a reconstructed, independently built CeTA 3.9 series.
