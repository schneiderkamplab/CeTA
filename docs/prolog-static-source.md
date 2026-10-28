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
