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
All ordinary cut transitions remain included. The relation supplied for a
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
