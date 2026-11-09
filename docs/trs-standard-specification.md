---
type: Formal Specification
title: "Ranked TRS Standard: specification and semantic correspondence"
status: draft
---

The definition-only package is separate from [derived properties](../thys/Category_Properties/TRS_Standard_Properties.thy)
and examples. See the [current package guide](category-specifications.md) for the three-layer layout.
# Ranked TRS Standard

## Reading order

1. [TRS_Standard_Spec.thy](../thys/Category_Specifications/TRS_Standard_Spec.thy)
   is the category definition. First read the shared
   [TRS_Spec_Base.thy](../thys/Category_Specifications/TRS_Spec_Base.thy),
   which imports only HOL `Main`.
2. [TRS_Standard_Examples.thy](../thys/Category_Properties/TRS_Standard_Examples.thy)
   exercises the definition independently of IsaFoR.
3. [TRS_Standard_Equivalence.thy](../thys/Category_Bridges/Bridge/TRS_Standard_Equivalence.thy)
   translates the mathematical objects and proves the semantic correspondence.
4. [TRS_Standard_Checker_Bridge.thy](../thys/Category_Bridges/Bridge/TRS_Standard_Checker_Bridge.thy)
   specializes the existing CeTA soundness theorems to Standard.

The specification is the object of mathematical review. Neither bridge is
imported by it. The equivalence proofs connect the existing checker semantics
to that independently stated property.

## Conventions

The variable type is polymorphic and required to be infinite by
`trs_problem`. Examples use natural numbers; CeTA uses strings. Terms are
finite trees. A signature is a partial arity function: `A f = Some n` permits
exactly arity `n`, and `None` excludes the symbol. A signature need not be
finite or contain constants. Rules form a finite set of ordered term pairs;
`trs_problem A R` requires both sides to respect the signature. It imposes
no left-side shape restriction and no right-side variable restriction.

Substitutions are total maps from variables to finite, possibly nonground
terms. Every image must respect the signature. A one-hole context contains
signature-correct sibling terms and respects the arity at each enclosing
node. `fo_step A R s t` means that both endpoints are signature-correct
and, for a rule `(l,r)` in `R`, a context `C`, and a correct substitution
`sigma`, `s = C[l sigma]` and `t = C[r sigma]`.

`trs_standard_terminates A R` is the absence of any infinite sequence of these
steps. It does not incorporate input validity as a Boolean conjunct: category
inputs separately satisfy `trs_problem A R`. Nontermination is exactly
its negation. This avoids classifying an invalid input as nonterminating.

## Theorem statements

- `trs_standard_nontermination_iff`: the negation of the canonical property
  is equivalent to the existence of `ts : nat => ('f,'v) fo_term` with
  `fo_step A R (ts i) (ts (Suc i))` for every `i`.
- `correct_term_iff`: `arity_correct A t` iff
  `funas_term (to_term t)` is a subset of `to_signature A`. Contexts,
  substitutions and rule collections have corresponding translation lemmas.
- `standard_step_iff`: `fo_step A R s t` iff
  `(to_term s, to_term t)` belongs to
  `sig_step (to_signature A) (rstep (to_rules R))`.
- `trs_standard_terminates_iff_signature`: the canonical property iff
  `SN (sig_step (to_signature A) (rstep (to_rules R)))`.
- `trs_standard_terminates_iff`: assuming `trs_problem A R`, the
  canonical property iff `SN (rstep (to_rules R))`.
- `trs_standard_terminates_iff_on`: under `trs_problem A R`, the
  canonical property iff ordinary rewriting terminates on all terms whose
  function/arity pairs belong to `to_signature A` (using `SN_on`).
- `trs_standard_nonterminates_iff`: under the same assumption, the negation
  of the canonical property iff `not SN (rstep (to_rules R))`.

The signature-restricted equivalence has no additional assumptions. In the
unrestricted equivalence, rule correctness provides the hypothesis of
IsaFoR's `SN_sig_rstep_imp_SN_rstep`. In particular no constant, groundness,
nonvariable-left-side, or variable-preservation assumption is added.

`trs_standard_checker_YES` and `trs_standard_checker_NO` assume:

- `trs_problem A R`, `tp_spec I`, and `dpp_spec J`;
- `tp_ops.nfs I tp = False` and `tp_ops.Q I tp = []`;
- `set (tp_ops.R I tp) = to_rules R` and `tp_ops.Rw I tp = []`;
- respectively, `isOK (check_trs_termination_proof I J False i tp prf)` or
  `isOK (check_trs_nontermination_proof I J False i tp prf)`.

In these checker corollaries the existing API fixes variables to `string`
and function symbols to CeTA's `('f, nat list) lab` type. The specification
and semantic equivalence remain polymorphic in both types.

Their conclusions are respectively `trs_standard_terminates A R` and
`not trs_standard_terminates A R`. The `False` checker argument disallows
certificate assumptions. These are semantic checker-input theorems, with all
Standard configuration fields explicit.

## Verification

The lightweight session is built with:

```sh
make isabelle-trs-standard-spec ISABELLE=/path/to/isabelle
```

The bridge session uses the repository's compatible AFP dependency tree:

```sh
make isabelle-trs-standard-bridge ISABELLE=/path/to/isabelle AFP="$AFP"
python3 scripts/check_okf.py docs
```

The examples cover an empty system, the terminating rule `f(x) -> x`, a
self-loop, rewriting below the root with a nonground substitution, arity
mismatches, and a signature with no constants. Before the shared-package refactor, both sessions passed a normal
Isabelle2025-2 build on 2026-11-07:
`TRS_Standard_Spec` (2 seconds) and `TRS_Standard_Bridge` (20 seconds).
The current checkout's dependency sessions were rebuilt successfully first.
A separate fresh-process bridge check also passed.
[Verification receipt](data/trs-standard-verification-20261107.json) records
source hashes, parent heap hashes, and log locations for that historical layout.
The corresponding sources are retained in `target/trs-standard/source-before-package/`.
Current package verification is recorded on the [package page](category-specifications.md).

The bridge includes a `Thm_Deps.has_skip_proof` audit of both equivalence
directions and both checker corollaries, including inherited dependencies.
It passes. The inherited library oracle names are `check_eqv` and
`cancel_type_definition`; this work introduces no oracle or axiomatization.

This milestone does not change certificate formats, generated checking code,
or production binaries. It establishes semantic correspondence; it does not
prove parser correctness or provide a new frontier replay.

## TPDB and input-path review

See the [2026-11-08 source and category review](trs-standard-input-review.md)
for confirmed TPDB conventions, concrete checker-module instantiation, and
outstanding benchmark-identity and frontend-validation obligations.

See the [integrated checker and trust boundary](trs-standard-trust-boundary.md)
for the concrete-module composition and runtime original-input gate.
