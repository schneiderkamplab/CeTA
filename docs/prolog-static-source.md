---
type: Verification Report
title: "Source-bound static Prolog checking"
status: draft
---
# Source-bound static Prolog checking

This branch adds `--category prolog` to the unified executable, built through
`make ceta`. The new Isabelle source theories are `LP_Prolog_Errors`,
`LP_Prolog_Static`, `LP_Prolog_Static_XML`, `LP_Prolog_Static_Audit` and
`LP_Prolog_Static_Code`. The source and export hashes are retained in
`scripts/unified-exports.json`. Generated checking logic has not been patched.

The accepted wrapper fixes the `iso-rational-libraries-v1` profile and proves
that reachable calls belong to a static predicate set disjoint from the fixed
builtin signature. The existing checked LP-with-cut SEG dependency-triple proof
then establishes termination. Arbitrary builtin steps are unreachable in these
states. Uncaught errors that discard the entire alternative stack preserve
termination; errors are not modeled as resuming a saved alternative. Numeric
literals may occur as opaque data, but this route proves no arithmetic evaluation
rule. Dynamic calls and builtin-dependent source proofs remain unsupported.

The signature uses the shared `arity:name` certificate encoding. It cannot be
chosen by the certificate. A negative test consistently renames a valid predicate
to `1:var`: its ordinary LP child remains valid, while the Prolog wrapper is
rejected. Other mutations cover profile, predicate coverage, source clauses,
query groundness and missing components. Ferrum separately audits the exact
original source, its selected preprocessing and query against the wrapper.

The LP adapter also accepts independently useful dependency-triple child proofs,
with the explicit verdict `CERTIFIED LP DEPENDENCY-TRIPLE CHILD`. This verdict
must not be interpreted as a source Prolog result. Prolog dispatch does not fall
back to that child checker.

Verification uses the existing verified v145 source heap read-only. Run
`scripts/verify_prolog_static.py` through `isabelle env`, supplying `--heap` and
`--log`. Optional `--export` regenerates Haskell into a new directory. The standard
session alternative is `Prolog_Static_Code`. The dependency audit rejects skipped
proofs and any oracle beyond the inherited rewriting-checker dependencies.

This is an isolated development integration in `CeTA-prolog-source`, branch
`codex/prolog-source`, based on main `8a3ccdd`. It has not replaced the installed
main checker. Full frontier replay, LeTA coverage and cross-repository release
integration remain required; these local checks do not establish production
release or full ISO Prolog certification.

[Retained validation evidence](prolog-static-validation.json.gz) records the
byte-identical clean re-export, theory audit, unified dispatch rejection tests
and all 408 protected semantic-negative rejections, with one checker hash.


## Source nontermination

The same unified checker now accepts static Prolog source NO certificates.
`LP_Prolog_Static_NO` defines ordinary resolution only when the active call is
neither builtin nor undefined; an undefined procedure aborts the complete stack.
The static NO connection requires every reachable static predicate to be defined.
The existing LP source-loop certificate then transfers with its checked stem,
loop and saved-stack closure. A second shared LP rule, in
`LP_Cut_Uniform_Recursion`, proves nontermination of a first universally matching
clause with a single same-predicate recursive call whose arguments use only head
variables. Arguments may grow or otherwise change indefinitely.

`LP_Prolog_Static_NO_XML` and `LP_Prolog_Uniform_NO_XML` provide the source
wrappers; `LP_Cut_Uniform_Recursion_XML` is reusable for ordered LP. All are
exported from Isabelle into the existing unified LP module. The dependency audit
covers the new source theorems and forbids admissions. Ferrum additionally audits
that a NO query decodes to an actual original Prolog query, including the source
symbol encoding and typed literals.

[NO integration validation](prolog-static-no-validation.json.gz) retains the
verified export log, source hashes, all 408 protected semantic negatives,
source/child checks and strict state-local replay. Seven Prolog YES results and
one Prolog NO result pass two checks each and strict replay. The NO is structural
changing-argument recursion in `Weinert_15/descend-nonterm.pl`; subtraction is not
executed there. Fifty-five extended DT children are independently checked but do
not establish source Prolog verdicts. Mutation controls include positive ordinary
LP certificates rejected by the stricter Prolog source wrapper.


## Finite undefined-entry errors

`LP_Prolog_Undefined_XML` proves termination when the declared entry signature is
absent from the complete source definition signature and the fixed builtin
signature. The only source transition raises an uncaught existence error and
discards the complete alternative stack. The empty state has no successor.
The result holds for every argument valuation, so it also covers all query modes.
No clause body is entered. Unsupported builtins are explicitly excluded.

The certificate records the complete ordered definition-signature list after
the selected source preprocessing, including explicit libraries. Ferrum audits
that list, the query, modes and profile against the original parsed source.
The formal theorem applies to every program with exactly that definition set;
unreachable clause bodies need no termination assumption. Changed source
signatures are source-audit failures, not additional axioms in the checker.

[Current validation](prolog-error-validation.json.gz) pins the regenerated export
and unified checker. All **14 source YES and one source NO** pass two checks and
strict state-local replay. Five new YES proofs are finite undefined-entry errors.
The existing verified negative-unification SEG rules additionally prove
`lateinstance.pl` and `divrempredef.pl`. A Ferrum writer bug that omitted the entry
encoding when there were no dependency triples was corrected; checker diagnostics
accepted the source graph and child separately while rejecting the incomplete
connection. The accepting checker was not weakened. Mutations now cover that
missing encoding and altered unification evidence as well as finite-error
builtin exclusion. All 408 protected semantic negatives still reject.

## 2026-11-04 Ground constructor fields in return contexts

Proof commit `b056904` lets the existing evaluation-context checker use explicit
ground observations when checking a constructor field's return shape. The proof
reuses `LP_Return_Shapes` and the same source execution relation. Groundness alone
does not establish a spine or an integer value; positive transport, missing
facts, unjustified shape and integer controls verify in Isabelle.

Integration `8f59b74` regenerates the eight-function export and builds unified
CeTA 312, SHA-256
`ee6dbcdaf7a8f41e605c7f52316493f99f2c1c92e7831e492d7ef94264d3da02`.
[Pinned proof and export evidence](data/prolog-ground-shape-20261104.json) retains
all attempts. Attempt 306 reused a finished theory and is explicitly excluded
as validation; 307 and 308 failed. The changed theorem verifies in 309, followed
by all updated controls and source dependencies in 310. Generated checking logic
was not edited.

The fix repairs three rejected graph connections in two already-retained
benchmarks. Fresh source and strict checks also accept a renamed fixture, while
removing required groundness or demanding a recursive spine rejects. Ferrum's
complete replay retains 59 YES and 3 NO on 221 Prolog inputs and 84 YES and 9 NO
on 112 LP-with-cut inputs, with two checks by this same executable. These are
preservation results, not new benchmark gains or a production promotion.
