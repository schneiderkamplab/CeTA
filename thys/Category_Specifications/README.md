# Rewriting category definitions

This package defines the mathematical questions. It contains definitions and
explanatory text only: no derived properties, examples, representation proofs,
checker connections, or proof-audit code. Its only external dependency is
Isabelle/HOL (`Main`). Copying this directory is sufficient to build it:

```sh
isabelle build -D /path/to/Category_Specifications
```

## Common vocabulary

Read [Rewriting_Sequences_Spec.thy](Rewriting_Sequences_Spec.thy) first.
`finite_steps step s t` permits zero or more steps. `no_infinite_steps step`
excludes a sequence indexed by all natural numbers whose consecutive elements
are related by `step`. Nontermination means the negation of that property.

For first-order categories, [TRS_Spec_Base.thy](TRS_Spec_Base.thy) supplies:

- `fo_term`: finite terms, with variables `SVar x` and applications `SFun f ts`;
- `ranked_signature`: a partial assignment of exactly one arity to each symbol;
- `arity_correct`: membership in the signature's term universe;
- `fo_subst`: simultaneous substitution, and `correct_substitution`: all images
  respect the signature;
- `fo_context`: a term with exactly one hole, and `fo_plug`: filling that hole;
- `correct_context`: the surrounding symbols and sibling terms respect the signature;
- `trs_problem`: finite, signature-correct rules over an infinite variable type;
- `fo_step`: a rule instance in any signature-correct context, with both endpoints
  in the signature's term universe.

The prefix `fo` means first-order. These objects are shared across all TRS
categories. Signatures need not contain constants or have finite domains. Rule
sets are finite; the source syntax may impose a finite declared signature.
Variables and nonground terms remain in scope. Variable left sides and new
right-side variables are allowed unless a category explicitly says otherwise.

Validity and termination are separate predicates. Read a category's termination
property together with its stated validity predicate. The definitions also give
meaning to relations outside valid inputs; this is not additional input coverage.

## Category reading order

| Category | Definition | Validity and final property |
| --- | --- | --- |
| TRS Standard | [TRS_Standard_Spec.thy](TRS_Standard_Spec.thy) | `trs_problem`; `trs_standard_terminates` |
| TRS Innermost | [TRS_Innermost_Spec.thy](TRS_Innermost_Spec.thy) | `trs_problem`; `trs_innermost_terminates` |
| TRS Relative | [TRS_Relative_Spec.thy](TRS_Relative_Spec.thy) | `relative_problem`; `trs_relative_terminates` |
| TRS Context-sensitive | [TRS_Context_Sensitive_Spec.thy](TRS_Context_Sensitive_Spec.thy) | `trs_problem`; `trs_context_sensitive_terminates` |
| TRS Outermost | [TRS_Outermost_Spec.thy](TRS_Outermost_Spec.thy) | `trs_problem`; `trs_outermost_terminates` |
| Conditional ordinary | [TRS_Conditional_Ordinary_Spec.thy](TRS_Conditional_Ordinary_Spec.thy) | `conditional_problem`; `trs_conditional_terminates` |
| Conditional operational | [TRS_Conditional_Operational_Spec.thy](TRS_Conditional_Operational_Spec.thy) | `conditional_problem`; `trs_conditional_operationally_terminates` |
| TRS Equational | [TRS_Equational_Spec.thy](TRS_Equational_Spec.thy) | `equational_problem`; `trs_equational_terminates` |
| SRS Standard | [SRS_Standard_Spec.thy](SRS_Standard_Spec.thy) | `string_problem`; `srs_standard_terminates` |
| SRS Relative | [SRS_Relative_Spec.thy](SRS_Relative_Spec.thy) | `string_problem` for both partitions; `srs_relative_terminates` |
| SRS Cycle | [SRS_Cycle_Spec.thy](SRS_Cycle_Spec.thy) | `string_problem`; `srs_cycle_terminates` |
| Higher-order | [Higher_Order_Sorts_Spec.thy](Higher_Order_Sorts_Spec.thy) | `higher_order_declared_problem`; `higher_order_terminates_over_sorts` |

Conditional rewriting first needs [TRS_Conditional_Spec_Base.thy](TRS_Conditional_Spec_Base.thy).
It defines ordered condition goals, successful finite derivations and evaluation
descent. Completed rewriting and potentially nonreturning evaluation are distinct
relations, hence two category properties.

SRS uses [SRS_Spec_Base.thy](SRS_Spec_Base.thy): words are finite lists and a step
replaces a contiguous segment. Relative rewriting requires infinitely many strict
steps for nontermination. Cycle rewriting permits rotation around a genuine
replacement; rotation alone is not a step.

Higher-order rewriting uses [Higher_Order_Spec_Base.thy](Higher_Order_Spec_Base.thy)
for types, binding, patterns and substitution, then
[Higher_Order_Spec.thy](Higher_Order_Spec.thy) for typed contextual steps.
The final declared-sort property is in `Higher_Order_Sorts_Spec.thy`:
all terms, environments and types use the source's declared sorts.
It includes beta reduction and designated meta-application, not arbitrary matching
modulo beta or eta. Its typed terms are intentionally distinct from first-order terms.

In Isabelle notation, `∀` and `∃` quantify, `⟷` defines logical equivalence,
`#` prepends to a list, `@` concatenates lists, and `!` selects a zero-based
list entry. `None` denotes an absent signature/type lookup; `Some A` denotes a
successful lookup. Premises of an inductive rule precede `⟹`; its conclusion follows.
