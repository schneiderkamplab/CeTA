# Theorem and problem-variant retirement

This follow-up supersedes the historical assessment's requirement to defer every
path without genuine replay coverage. The user authorized formal refactoring of
those paths. Missing replay evidence remains a reported coverage gap, not an
approval requirement or an automatic prohibition on simplification.

## Implemented unifications

1. **Finite conservative coverage:** `finite_conservative_csdp_coverage` now
   specializes `conservative_csdp_coverage` with `restrict_mu_to_sig F mu`.
   The new `finite_conservative_csdp_coverage_iff` proves the complete old
   characterization, including projection coverage only within F. The checker
   refinement uses that characterization. The old one-way bridge is a direct
   corollary. This retires an independently maintained semantic definition,
   without dropping the signature restriction or changing the child problem.
2. **Endpoint deletion:** `SN_rel_min_endpoint_order` is a corollary of
   `SN_rel_min_endpoint_order_lookahead`. Its stronger local premises discharge
   the lookahead obligations without using the two subsequent pair events.
   Its independent infinite-chain proof is retired. All nine assumptions,
   including target termination, both compatibility directions, transitivity,
   residual finiteness and connector ordering, remain unchanged.
3. **Partial natural ranks:** the plain, pair and normalized-pair termination
   theorems specialize `SN_partial_nat_rank` and `SN_rel_partial_nat_rank`.
   Six separate proof implementations are retired. Both endpoints must still
   have `Some` ranks; this does not assign an arbitrary measure to `None`.
   The three rank functions and their relations remain distinct.

The eight replaced named theorems retain their original statements as
compatibility corollaries. Removing their names would break clients without
reducing the semantic implementation further. The definition theorem
`finite_conservative_csdp_coverage_def` now expands to the specialization;
clients needing the original explicit clauses use the new `_iff` theorem.
The production checker refinement has been migrated accordingly.
`theorem-retirement-audit.json` records all eight unchanged theorem statements,
lexical source references, and hashes of the changed theories. Isabelle builds,
not this lexical index, validate actual theorem dependencies.

## Decisions on the other proposed retirements

| Variants | Decision and concrete reason |
| --- | --- |
| Minimal/nonminimal CSR DPs | Keep both. `csr_min_pair_step` filters root pair steps by target `SN_on`; `finite_csr_dpp_imp_finite_min_csr_dpp` proves one direction only. The standalone nonminimal checker deliberately rejects processors that require minimality. A common tuple with `False,False` ordinary flags does not eliminate this CSR distinction. |
| Full/innermost CSR DPs | Keep both modes. `finite_mode_csr_dpp_full` already identifies the full specialization. The innermost relations additionally require active proper subterms to be normal forms; subset lemmas do not establish the reverse implication. |
| Conservative/improved CSDPs | Keep both constructions. Conservative coverage supplies projections and marking in the auxiliary TRS S and checks an ordinary DP obligation over S. Improved coverage places hidden/unhiding pairs in P and its guarded checker proves minimal CSR-chain finiteness over the source R. The finite conservative wrapper is unified above, not coerced into improved CSDPs. |
| Typed/non-typed MU-TERM | Keep typed semantics. `muterm_typed_pair_step` includes collapsing-pair composition with the unhiding relation. Existing noncollapsing bridge theorems have an explicit noncollapsing premise; they do not cover arbitrary P. |
| Typed full/minimal/innermost/I4/extended-basic | Keep the filters visible. Full minimality intersects with target `SN_on`; innermost minimality uses a marked `mu_Tinf` target; I4 additionally intersects with `i4_chain_good` at both endpoints; extended-basic restricts targets to marked full-CSR `mu_Tinf`. Existing implication lemmas do not prove these predicates equal. |
| Direct innermost/RTA08/exact unhiding | Keep construction-specific coverage. Their hidden/collapsing pair and bridge obligations remain different. No general replacement theorem has been established in this batch. |
| CSR switch/AAECC switch | Keep distinct criteria. `csr_switch_overlay_innermost_termination` concerns `csstep mu R` and `innermost_csstep mu R`, under its overlay condition. `aaecc_innermost_termination` concerns ordinary rewriting of `R1 union R2`, with signature separation, R1 conditions and absence of cross critical pairs. Neither name nor common termination conclusion supplies the missing premises. |
| Guarded terminal/endpoint/lookahead/alternating | Keep accepted forms and the alternating criterion. Ordinary endpoint deletion is now a corollary. Alternation supplies strict progress across successive pairs without a residual-finiteness premise; no replacement by the residual theorem is claimed. The concrete ovcons semantic theorem already delegates to `finite_min_csr_dpp_guarded_two_pair`. |
| Usable-rule algorithms | Keep mode-specific refinement obligations. Ambient R, source R, minimality, innermost normality and typed pair composition cannot be erased merely because executable closure code looks similar. This batch establishes no common refinement theorem for all modes. |
| GM04 full/complete/sanitizing and residual adapters | Keep explicit signature/freshness, Q, minimality and child-assumption contracts. Standalone residual checking is not a fresh DP construction. Earlier executable guard cleanup is separate evidence, not permission to drop further assumptions. |
| Relative ADP erasure/Com and ordinary QDP | Keep annotations, main/base partitions, repositioning and distinct order obligations. The earlier shared renaming extraction does not equate these problems. |
| RFC absolute/relative residual | Keep both child contracts. `SN_from_RFC_delete_and_absolute_residual` explicitly needs global termination of K in addition to the RFC-restricted relative result. The absolute adapter cannot replace the relative residual obligation without proving that extra premise. |
| Outermost RZ/ordinary termination | Keep the transformation. Its generated full-TRS child proves an outermost source claim under cover, pattern and freshness conditions; it is not an ordinary-source termination criterion. |
| Historical unmerged development variants | Keep frozen comparison history; do not import or delete excluded uncommitted work. Retiring a production implementation is separate from deleting historical branches in other worktrees. |

These are decisions about the stated contracts, not universal proofs that no
further mathematical unification is possible. Additional retirement requires a
specific implication/equivalence proof and caller migration. Positive benchmark
overlap is not such a proof. No distinct problem kind or CPF form is removed.

## Verification

All gates passed; `theorem-retirement-verification.json` records the result and
`theorem-retirement-evidence.json.gz` retains source identities, complete logs,
receipts, per-theory timings, compact results and controlled performance repeats.

All five production/integration targets and the focused guarded session passed.
All 398 ordinary, 401 RFC and 9 relative exported modules are byte-identical to
the previous verified outputs. Clean GHC builds reproduce all three binaries
byte-for-byte. The compact suite passed 208 positives and 408 semantic negatives,
with twice production certification, HPC agreement, and all 45,733 retained
obligations. The original denominator remains 45,753, with 20 previously retired
counters reported separately. Three production and one HPC timing outliers were
cleared by alternating reference/candidate repeats; no slowdown was confirmed.
The harness also passed its 12 tests.

The full 3,484-root replay evidence is reused by exact checker identity. This
batch did not regenerate Ferrum proofs or snapshot the current live frontier.
Genuine relative-ADP processor and positive outermost RZ replay gaps remain
explicit. Runtime checks are separate from the Isabelle proofs above.

 Three endpoint proof-script attempts failed: `auto` split the union conclusion
before using its premise, and chained facts interfered with the initial `rule`
application, followed by an unintended higher-order relation instantiation. The
final script fixes all five relations explicitly and discharges each premise
separately. Failed attempts remain in the
evidence logs and are not counted as passing checks.
