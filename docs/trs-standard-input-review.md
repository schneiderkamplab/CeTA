---
type: Historical Report
title: "TRS Standard: TPDB definition and input-path review"
status: draft
---
# TRS Standard: TPDB definition and input-path review

Review date: 2026-11-08. Scope: current TPDB/TermCOMP ARI definition,
local source inspection, and focused existing audit/dispatcher tests. This is
not a formal parser-correctness proof or a new full benchmark replay.

## Category definition

The authoritative [TermCOMP term-rewriting page](https://termination-portal.org/mediawiki/index.php?title=Term_Rewriting&oldid=2024)
explicitly overrides CoCo's variable restrictions: rules may be arbitrary term
pairs. Standard uses full rewriting and arbitrary start terms; non-relative
categories disallow rule costs. Thus allowing variable left sides and extra
RHS variables in our specification is intentional category compatibility,
not merely a permissive generalization.

The linked [ARI TRS syntax](https://project-coco.uibk.ac.at/ARI/trs.php) declares
each function symbol once with a fixed arity. Undeclared identifiers are
variables; applications must respect declared arities. Its usual variable
conditions are overridden by TermCOMP's explicit exception. Unused function
declarations are permitted. These conventions agree with our ranked terms,
nonground substitutions and arbitrary contexts. The specification permits
infinite signatures as a mathematical generalization; finite input declarations
are included. It does not formalize identifier syntax.

## CeTA parsing and dispatch

1. [Main_Unified.hs](../src/Haskell/Main_Unified.hs) selects the CPF adapter
   by default or with `--category cpf`. It does not assert the TPDB subcategory
   Standard; that distinction is represented in the parsed input.
2. [Rewriting.hs](../src/Haskell/Ceta/Category/Rewriting.hs) starts with
   assumptions disabled and calls `certify_proof_integrated`. The explicit
   `--allow-assumptions` flag changes that premise and lies outside our bridge.
3. [Relative_ADP_Ceta.thy](../thys/Relative_ADP/Integration/Relative_ADP_Ceta.thy)
   parses once and dispatches between ordinary and relative-ADP proofs.
   `certify_integrated_cert_problem_sound` proves `desired_property` after
   successful assumption-free checking. It supplies the concrete proofs
   `tp_rbt_impl`, `dpp_rbt_impl`, `ac_tp_list_impl`, `ac_dpp_rbt_impl` itself.
   Thus the existing integrated theorem already discharges the module
   contracts at the parsed-input level. The new category bridge has not yet
   been composed with this integrated theorem in its own session.
4. [CPF_Input_Parser.thy](../thys/Proof_Checker/CPF_Input_Parser.thy) builds
   `Fun name args` and `Var name`, including indexed terms/rules. Ordinary
   rules reject nonempty conditions. `trs_input` defaults to `No_Strategy`
   and an empty weak-rule list when these elements are absent. It accepts
   other strategies and weak rules when explicitly supplied; being sent to
   the CPF adapter does not enforce Standard.
5. [Ceta_Problem_Spec.thy](../thys/Proof_Checker/Ceta_Problem_Spec.thy) maps
   `No_Strategy` to `nfs=False` and empty Q. For
   `Inn_TRS_input No_Strategy R []`, termination decisions mean ordinary
   termination/nontermination of R.
6. [Proof_Checker.thy](../thys/Proof_Checker/Proof_Checker.thy) checks matching
   input/property/answer combinations. The ordinary YES branch constructs
   the termination problem with those strategy fields and rule lists. The
   ordinary NO branch explicitly checks that weak rules are empty. Extended
   integrated branches retain their own soundness proofs.

The CPF TRS input carries no TPDB declared signature. Its term parser does not
validate applications against an external ARI signature. For a faithfully
translated, valid Standard benchmark, our proved signature-extension result
handles the unrestricted checker term universe, including unused declared
symbols. It does not establish faithful translation of an arbitrary input file.

## Original benchmark identity is a separate obligation

CeTA normally checks the problem embedded in the certificate. It does not read
the original ARI benchmark or its category directory in this invocation.
[CPF_Parser.thy](../thys/Proof_Checker/CPF_Parser.thy)'s `parse_merge` gives
explicit `--inputf`, property and answer arguments precedence over embedded
values; this is replacement, not a comparison of both copies. `--inputf`
expects a CPF input element, not an ARI file.

Consequently, acceptance alone does not say that the certificate describes the
benchmark the caller intended. Rules, variable sharing, symbol identity,
strategy and decision polarity must be bound to that benchmark independently.
The existing [root-input audit](../../ferrum/docs/trs-root-input-audit.md)
provides historical finite-corpus evidence. Its current
[audit implementation](../../ferrum/scripts/audit_trs_root_correspondence.py)
checks original ARI declarations/arities, rule multisets up to per-rule variable
renaming, strategy and answer. This review does not claim it is automatically
run on every production invocation.

## Ferrum ARI frontend findings

Source inspection of [ari.rs](../../ferrum/src/parsing/ari.rs) found the following
limits in the ordinary `parse_ari_trs` route:

- `declared_symbols` retains names but not declared arities; this route does
  not validate applications against declared arities or reject duplicate
  declarations. Internal term-arity consistency checks are not a substitute
  for comparing with the declarations.
- `strategy_from_source_name` searches the path for `outermost` or `innermost`,
  otherwise choosing Full. Renaming/moving a file can therefore change the
  inferred strategy; explicit category binding must be checked separately.
- Empty rule sets are rejected, though the category syntax permits them.
  Positive rule costs are accepted as strict by the shared rule parser,
  although Standard disallows costs. These are input-coverage/validation gaps.
- `ari_term` strips leading question marks from atomic variable names before
  considering declared symbols. This is an additional normalization requiring
  justification or rejection under the identifier rules; it must not merge
  distinct benchmark identifiers.

These observations identify frontend obligations, not demonstrated false
acceptances by CeTA. A proof about the parsed system still needs the original
input correspondence check. No parser or production code was changed during
this review.

## Verification and disposition

All 14 existing root-correspondence unit tests passed. The installed `CeTA/ceta`
passed the dispatcher test: listed categories match expectations, malformed
inputs are not certified, and invalid category arguments fail. This is a narrow
negative/dispatch check, not a replay of all Standard certificates. Commands,
outputs and the tested executable hash are retained in the
[review test record](data/trs-standard-review-20261108.json).

The Standard mathematical definition matches the checked category conventions.
Concrete module correctness is already available in the integrated soundness
theorem. The remaining end-to-end work is to compose that theorem with the new
canonical specification and establish/enforce original-input and category
binding along the deployed path. Frontend validation issues above remain open.

## Follow-up: ordinary frontend hardening

The subsequent [Ferrum input-contract change](../../ferrum/docs/ari-input-contract.md)
addresses the ordinary-parser findings above: declaration validation, exact
category paths, an explicit rewrite-strategy option, empty rules, rejected costs
and preserved question-mark identifiers. The review above describes the
pre-change findings. Existing correspondence strategy checks were retained
and strengthened with regressions for both answer polarities; proof-type
compatibility is checked by CeTA. Other category frontend audits and the
formal parser-to-specification correspondence remain open.
