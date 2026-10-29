---
type: Verification Report
title: "Prolog extension: shared return graphs and rational projections"
status: draft
---
# Prolog extension: shared return graphs and rational projections

The extension reuses the LP-with-cut stack, answer environments and graph
progress argument. `LP_Answer_Graph` factors the existing termination and
return-path lemmas over an arbitrary answer-labelled transition relation.
`LP_Cut_Return_Contracts` retains its public definitions and theorems and now
uses those shared lemmas. This is a theorem refactor, not a new LP acceptance
rule.

`LP_Prolog_Answers` adds an explicit interface for atomic builtin success,
failure and uncaught errors. Success substitutes only the active continuation
and its return environment. Failure resumes saved alternatives with their saved
environments. An uncaught error clears the entire stack. Erasure, source-step
lifting, termination transfer and the extended return contract are proved.
Ordinary cut transitions are inherited except at a recognized builtin call,
where builtin dispatch takes precedence. Exact single-outcome lemmas exclude a
spurious failing clause-lookup branch before a cut. The relation supplied for a
builtin must itself be justified: this interface neither proves finite builtin
evaluation nor handles enumerating builtins with internal choice points.
There is no executable source-certificate acceptance for this interface yet.

`LP_Prolog_Graph_Projection` gives an executable checker for finite projections
of rational value graphs. Its soundness theorem establishes `lp_iproject`;
corollaries establish groundness and stability under substitution. The checker
follows only selected edges, so cycles in discarded arguments are permitted.
A retained cycle cannot obtain a finite projection by consuming an encoding-size
measure. The graph-equation lemma establishes simultaneous satisfiability of
rational-unification equations. It does not by itself prove Ferrum's complete
relational triples transformation.

The projection checker is exported through `LP_Prolog_Static_Code` and the
unified LP archive. Generated Haskell is regenerated with
`scripts/verify_prolog_static.py`, never patched. `LP_Prolog_Static_Audit` checks
all new bridge and projection theorem dependencies for skipped proofs and
oracles beyond the inherited checker dependencies.

Local verification artifacts are in `target/prolog-extended/`:
`projection-only.log`, `answers-only.log`, `audit-export.log` and
`answer-audit-export.log`. Failed initial attempts remain local evidence; the
successful runs end in `PROJECTION_VERIFIED`, `ANSWERS_VERIFIED` or
`PROLOG_STATIC_VERIFIED`, respectively. The first projection export's unified
binary has SHA-256
`8351ed84ce94f84d561977dfbe9f63bfd14c4bfe4947cb9470beeadd8e6c8dd7`.
Ferrum's `target/prolog-extended-checker/` records 274 successful checks of 15
Prolog, 93 cut and 29 partial CPF certificates, plus 58 checks of freshly
replayed CPF components. Arithmetic fixture children have four further checks.
These checks preserve existing source results; no additional certified Prolog
source verdict or production release is claimed.

The remaining acceptance work is concrete: verified primitive evaluation and
local SEG coverage; return/split coverage for the extended relation; a checked
source parser/bridge; and reconstruction from all independently checked PiDP
and ITS children. Native type inference, projected residuals and successful
child proofs cannot discharge these obligations implicitly. Mixed integer and
structural cycles remain open pending the separate constrained-DP backend.

[Durable Isabelle audit and export log](prolog-extension-audit-20261029.log.gz)
records successful replay of the shared cut theorems and the new extension
theorems. The final re-export is byte-identical to the first projection export;
its generated-module SHA-256 is
`b250c62334faaa23aa080ffcff491edeec5c73a9d1a3e853287ec96112d61d31`.
The manifest also pins the shared graph and refactored cut-contract theories.

The dispatch refinement changes only unexported extension theorems. The
accepted static source-certificate language and generated checking code remain
unchanged. The recognized builtin set and interpreted outcome relation are
explicit proof parameters; an accepting source bridge must check both.

[Dispatch refinement audit](prolog-dispatch-audit-20261029.log.gz) checks the
updated source instrumentation, return contract and exact builtin-outcome
lemmas, including their dependencies. No skipped proof or new oracle is used.

## Executable variable-test source bridge

The shared return table now checks `var/1` and `nonvar/1` in the selected
source profile. Unknown shapes require both outcomes; constructors and checked
groundness establish nonvar. Successful tests preserve the active answer
environment, failure restores the saved alternatives, and the root theorem
also permits uncaught errors that stop execution. Other builtins and dynamic
calls remain outside this source fragment. The complete original program,
query modes, table, residual program, role encoding and dependency-triple
child are checked together. Ordinary LP dispatch rejects this extended format.

`LP_Prolog_Return_Check` delegates ordinary frames to the existing cut checker
and uses the shared transition-parameterized answer-graph theorem. It does not
introduce a parallel SEG or erase return environments. The fixed builtin
signature moved to its own theory without changing its members. Native free
variable facts are not assumed by this first coverage rule.

[Full Isabelle dependency audit and generated export](prolog-var-return-audit-20261029.log.gz)
passes without skipped proofs or additional proof oracles. `make ceta` builds
one unified executable, SHA-256
`956f47b46b30f67fe2d4c73581803d9c26479bf84a47e0fcd7062d5f89254503`.
The export is regenerated from Isabelle; generated checking logic is not patched.
Four positive fixtures and their strict replays pass twice. Nine semantic or
structural mutations are rejected, including missing outcomes, lost saved
alternatives, changed source clauses and lost entry groundness. The same
executable preserves 15 Prolog source certificates, 93 cut source certificates
and 29 retained residual certificates, each checked twice. Dispatcher rejection
tests pass. Artifacts are retained in Ferrum's `target/prolog-var-*` directories.

This adds an accepting certificate family, not benchmark coverage: the Prolog
frontier remains 14 YES and one NO. Extended split coverage, other builtin
semantics, full rational/functor projection checking and complete ITS/PiDP
parent reconstruction remain open. Mixed cycles remain open as requested.

## Identity-test equations and two additional source YESs

The same return-table constructor now supports `==/2` and `\==/2`. Equality is
an observation of the current values, not an instruction to bind them. Only
the equality outcome supplies equations to the shared checked normalization
and linking rules; the other outcome retains its unconstrained interface.
Saved alternatives and their answer environments participate in the checked
link. A syntactically identical operand pair has one feasible outcome; otherwise
both are checked. Cyclic conditional normalizations that native search cannot
represent remain open.

The combined builtin relation retains the previous variable-test semantics.
`LP_Prolog_Identity_Test` proves local coverage and conditional equations, and
its source theorem is composed through the existing shared return table and
PiDP child. [The full dependency audit and regenerated export](prolog-identity-return-audit-20261029.log.gz)
pass without proof admissions or additional oracles. Unified CeTA SHA-256 is
`3894a20eb211f3cf412f57ccbb730318990f054d0f078fd2f1afa1e70816e306`.

`equality1.pl` and `equality2.pl` now have complete source YES certificates,
each independently checked twice, including fresh strict replay. Ten positive
checks cover these discoveries/replays and a negative-identity fixture; eight
equality-certificate mutations are rejected. All nine variable-test mutations
remain rejected. The same executable preserves 145 retained source, residual
and fixture certificates twice, including all 93 cut results. Dispatcher tests
pass. Ferrum's full 221-input strict source replay yields **16 YES, one NO and
204 unresolved/rejected**; no existing source result is lost. This is a new
source frontier, not completion of extended Prolog certification or a release.

## Test-bearing nontermination prefixes

The executable `prologTestSourceNonterminationProof` checks an exact prefix
containing `var`, `nonvar`, `==` and `\==`, then reuses the ordered LP-with-cut
loop/pending-stack pumping theorem. The local component check retains the
complete original program, requires all component predicates to be defined and
non-builtin, and checks every relevant clause body. Undefined calls cannot be
traversed as ordinary failure. Finite witness terms embed injectively into the
rational runtime model; this route does not yet execute cyclic unifiers.

Isabelle verifies the prefix steps, reachability, component preservation, pump
transfer, XML root theorem and dependency audit. The unified checker is
regenerated without generated-code edits. Its SHA-256 is
`38fec526bfee085d73c7f68a0437755c7d231d9d076dd19e8f8bcc003373ad73`.
Ferrum's fresh full strict replay retains 16 YESs and two NOs across 221 Prolog
roots; `inequality1.pl` is the new NO. Four fixtures also pass strict replay.
Twelve negative checks reject, including wrong-category dispatch. The same
checker preserves 162 retained certificates twice, including 93 cut proofs.
Thirteen malformed dispatcher invocations reject. This is a development
checkpoint; rational/functor source projection and arithmetic source proofs
remain incomplete.

The [audit log](prolog-test-no-audit-20261029.log.gz) records verified export.
Full source replay, mutations and preservation evidence are retained in the
sibling Ferrum worktree under `target/prolog-test-no-*` and its durable
`docs/data/prolog-test-no-frontier-20261029.tar.gz` checkpoint.

## 2026-10-29 Shared return modules

The Prolog return checker now instantiates language-independent answer contracts
for barrier trimming and complete alternative-stack decomposition. Ordinary
LP-with-cut return contracts are instances of the same interface. Each module
link must descend in the checked residual; saved answer tuples, scope transport,
entry assumptions and all alternative children remain explicit. A guarded
refutation reuses the existing checked cut rule.

Isabelle verified the source-root theorem and regenerated the module XML checker;
[the complete audit](prolog-return-module-audit-20261029.log.gz) is retained.
The `make ceta` unified executable has SHA-256
`51ba973bd2e0d53f3f2e350569f4b30775e70b12b7ca080fb9d2a554939d176e`.
Twelve new module certificates pass twice; thirteen fixture checks include two
positive checks and eleven rejection checks. All 181 retained certificates pass
twice, including 93 LP-with-cut certificates. Thirteen malformed dispatcher
cases reject. Ferrum's full strict 221-root replay preserves 17 YES and two NO;
three module fixtures pass strict replay, and missing child guidance is UNKNOWN.
No new benchmark root or production-release claim follows from this extension.
Artifacts are in `target/prolog-extended/module-*` and sibling Ferrum's
`target/prolog-return-module-*`.
