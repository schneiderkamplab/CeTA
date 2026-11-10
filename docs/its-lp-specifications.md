---
type: Formal Specification
title: "ITS and logic-programming category specifications"
status: draft
---
# ITS and logic-programming category specifications

This review extends the definition-only [category package](category-specifications.md)
to integer transition systems, definite logic programs and logic programs with cut.
The separate Prolog category is excluded. Finite-term, rational-tree and arbitrary-infinite-tree LP
semantics have separate final predicates; none is an alias for another.

## Reference semantics

The [current ITS category description](https://termination-portal.org/wiki/Integer_Transition_Systems)
requires one declared entrypoint and considers all well-sorted value arguments
there, including integers and Booleans. The specification expresses execution
as a finite collection of guarded transitions on mathematical integer stores.
Boolean slots can be represented by 0/1 with an explicit permitted-store
predicate. Pre-state, post-state and existential local stores are separate;
updates are simultaneous. Location assertions constrain both endpoints.
The execution definitions also apply to multi-entry systems, but `its_problem`
requires exactly one entrypoint. Relational guards separate execution semantics
from arithmetic syntax and parsing.

The [current competition reference, LP chapter](https://github.com/TermCOMP/termcomp-reference/blob/main/lp.tex),
sections “Semantics” and “The Occurs-Check”, explicitly requires leftmost
most-general resolution over finite terms with the occurs-check. It also
specifies ground/arbitrary query modes and standardization apart. This resolves
the earlier uncertainty: finite-term LP is the primary competition property.
The historical portal's LP-Prolog exception is not the rule for this category.

The same chapter identifies [the TPLP cut calculus](https://arxiv.org/abs/1007.4908)
as the basis of LP with cut. Its finite-term, ordered, scoped-cut execution is
the primary cut presentation here. Rational and arbitrary-infinite runtime
trees are separately named variants, not replacements for the primary spec.
No user confirmation is needed for this choice.

## Reading order

1. [ITS_Spec](../thys/Category_Specifications/ITS_Spec.thy): stores, transitions,
   initial states and termination.
2. [LP_Terms_Spec](../thys/Category_Specifications/LP_Terms_Spec.thy): shared finite
   terms, runtime trees, finite/rational domains and substitution.
3. [LP_Spec_Base](../thys/Category_Specifications/LP_Spec_Base.thy): clauses,
   most-general resolution, query modes and universal termination.
4. [LP_Finite_Spec](../thys/Category_Specifications/LP_Finite_Spec.thy) and
   [LP_Rational_Spec](../thys/Category_Specifications/LP_Rational_Spec.thy): the finite and rational
   final properties.
5. [LP_Cut_Spec_Base](../thys/Category_Specifications/LP_Cut_Spec_Base.thy): ordered
   backtracking, invocation scope, most-general unification and meta-call decoding.
6. [LP_Cut_Finite_Spec](../thys/Category_Specifications/LP_Cut_Finite_Spec.thy) and
   [LP_Cut_Rational_Spec](../thys/Category_Specifications/LP_Cut_Rational_Spec.thy).

All clauses and initial queries are finite in every LP variant. Rational runtime
trees have finitely many distinct subtrees. The separate
[LP_Infinite_Spec](../thys/Category_Specifications/LP_Infinite_Spec.thy) and
[LP_Cut_Infinite_Spec](../thys/Category_Specifications/LP_Cut_Infinite_Spec.thy)
also admit non-rational infinite trees; they retain exact most-generality.
An arbitrary query argument can be a compound nonground term and can share
variables with other arguments. Groundness does not mean that all query arguments
are ground. Most-generality includes continuation and clause-body variables,
so an otherwise unconstrained variable cannot be arbitrarily specialized.

For cut, success resumes saved alternatives. Resolution substitutes only the
active goal and clause body, leaving saved alternatives intact. Meta-calls have
separate cut scopes; an unbound or malformed callable is a finite error.
An infinitely unfolding cyclic conjunction is represented as divergent decoding,
not as a failed call. These extensions beyond the finite reference calculus
require explicit review; the broader Prolog language is not specified.

## Proof obligations and coverage

The HOL-only [properties](../thys/Category_Properties/LP_Properties.thy) keep
examples and derived facts outside the specification directory. In particular,
they distinguish the cyclic equation `X = f(X)` in the two domains and check
query groundness, scoped pruning and resumption after success.

The [ITS bridge](../thys/Category_Bridges/ITS_Bridge/ITS_Equivalence.thy)
encodes native typed valuations, initial states and single steps, and connects
infinite executions in both directions. Its concrete checker connection targets
`check_its4`, including termination, ground nontermination and recurrent-region
and recurrent-cycle certificates.

The [LP bridge](../thys/Category_Bridges/LP_Bridge/LP_Representation.thy)
structurally translates runtime trees and source clauses. Exact most-general
resolution is simulated by the existing all-unifier infinite-tree YES calculus.
The serialized YES corollaries conclude finite, rational and
arbitrary-infinite-tree LP termination, with source program and query modes
explicitly bound. The [additional family bridges](../thys/Category_Bridges/LP_Bridge/Families/LP_Yes_Category_Bridges.thy)
cover constructor, residual constructor, PiDP, PiDP mode, simplification,
source graph, SEG, residual, initial triples and the finite-named artifact.
Together with TOCL09 these cover the eleven concrete pure-LP YES endpoints
in the unified dispatch. The finite-named artifact uses the same Boolean check
as TOCL09; its stronger domain result follows from that check's existing theorem,
not from changing or assuming the meaning of its format name.
This simulation is not an equivalence and cannot be reversed for NO.

The [cut representation](../thys/Category_Bridges/LP_Bridge/LP_Cut_Representation.thy)
preserves user/control symbols, ordered clauses, substitutions, saved alternatives,
scopes and meta-call decoding. It simulates canonical unrestricted-tree steps by
the native YES relation. The serialized cut-table corollary binds the exact
program and query to `check_lpc_xml` acceptance. The original unrestricted-tree
connection is retained alongside the new domain-specific proofs below.

The finite/rational work is separate. The
[solved-substitution proofs](../thys/Category_Bridges/LP_Bridge/LP_Cut_Finite_Unification.thy)
show that an accepted finite substitution is most general within each domain:
the competing solution itself supplies a factor in that domain. The
[coverage lemmas](../thys/Category_Bridges/LP_Bridge/LP_Cut_Domain_Guards.thy)
interpret actual match, clash and equality checks in the chosen domain. Locale
closure premises are discharged for finite and rational trees; these premises
are not extra assumptions on certificates. The
[domain checker bridge](../thys/Category_Bridges/LP_Bridge/Checker/LP_Cut_Domain_Checker.thy)
now propagates that interpretation through knowledge, node checks, links,
resolution, equality, control, answer sequencing and the complete table theorem.
It proves finite-term and rational-tree YES directly from the unchanged
`check_lpc_xml` acceptance event. Failed unification is interpreted in the
selected domain throughout; this is not a transfer of infinite-tree termination.

The [execution properties](../thys/Category_Properties/LP_Cut_Execution_Properties.thy)
prove that injective renaming of invocation scopes preserves canonical steps.
The [cut examples](../thys/Category_Properties/LP_Cut_Examples.thy) establish empty
program termination in all domains and finite errors for unbound meta-calls.
All remain outside the definition-only package. The
[checked pumping example](../thys/Category_Bridges/LP_Bridge/NO/LP_Cut_Domain_NO_Examples.thy)
accepts the two-step loop of `p :- p` and derives canonical finite/rational
nontermination despite its growing invocation-barrier stack.

The [constructor-graph bridge](../thys/Category_Bridges/LP_Bridge/Families/LP_Cut_Constructor_Category_Bridge.thy)
reuses the domain root-table theorem with the concrete constructor residual
checker. Its finite, rational and unrestricted-tree corollaries have only exact
parse and acceptance premises.

The [MGU bridge](../thys/Category_Bridges/LP_Bridge/MGU/LP_Cut_Domain_Precise_Checker.thy)
connects `check_lpc_mgu_constructor_xml` to all three canonical predicates.
The proof preserves most-generality over the selected domain, including the
whole continuation and clause body, and uses domain-specific failure. It covers
all table actions, free-variable links and the concrete constructor residual.
Its final premises are the exact parse result and actual checker acceptance.

The [return bridge](../thys/Category_Bridges/LP_Bridge/Returns/LP_Cut_Domain_Return_Checker.thy)
and [module bridge](../thys/Category_Bridges/LP_Bridge/Returns/LP_Cut_Domain_Return_Module_Checker.thy)
cover constructor and dependency-triple endpoints in all three domains. Their
shared proofs retain saved environments, distinguish success from failure,
justify scoped links and establish strict residual descent. Module contracts
also cover barrier trimming and singleton-stack combination.

The [NO bridge](../thys/Category_Bridges/LP_Bridge/NO/LP_Cut_Domain_NO_Checker.thy)
interprets the existing `check_lpc_no_xml` certificate in each domain. Checked
finite solved substitutions supply domain-valued MGUs and factors. The proof
covers resolution, output-variable swaps, equality, failure, administrative
steps and function-root meta-calls, followed by the checked prefix and
scope-renamed pumping of barriers or safe pending alternatives. It constructs
an infinite canonical execution; it does not reverse the YES overapproximation.
The same certificate family can therefore establish NO for finite, rational
and arbitrary-infinite trees when its exact source and query match.

The checked theorem boundaries are:

| Theorem | Premises | Conclusion |
| --- | --- | --- |
| `its_termination_iff` | None | Canonical termination of the translated ITS iff native LTS termination |
| `its_checker_yes` / `its_checker_no` | Concrete `check_its4` accepts the respective verdict | Canonical termination / its negation |
| `its_serialized_decision` | Exact CPF parse result and serialized checker acceptance | Canonical termination equals the parsed answer |
| `lp_tocl09_category_yes` | Exact TOCL09 parse result, checker acceptance, ground-position set equals query modes | Canonical pure-LP termination in each of the three domains |
| `lp_cut_table_finite_yes` / `lp_cut_table_rational_yes` | Exact cut-table parse result and `check_lpc_xml` acceptance | Canonical finite-term / rational-tree cut termination |
| `lp_cut_table_infinite_yes` | Exact cut-table parse result and `check_lpc_xml` acceptance | Canonical arbitrary-infinite-tree cut termination |
| `lp_cut_return_{finite,rational,infinite}_yes` / `lp_cut_return_triples_{finite,rational,infinite}_yes` | Exact return parse and concrete constructor/triple acceptance | Canonical cut termination in the respective domain |
| `lp_cut_return_module_{finite,rational,infinite}_yes` / `lp_cut_return_module_triples_{finite,rational,infinite}_yes` | Exact module parse and concrete constructor/triple acceptance | Canonical cut termination in the respective domain |
| `lp_cut_return_composed_{finite,rational,infinite}_yes` / `lp_cut_return_composed_triples_{finite,rational,infinite}_yes` | Exact composed parse and concrete constructor/triple acceptance | Canonical cut termination in the respective domain |
| `lp_cut_return_nested_{finite,rational,infinite}_yes` / `lp_cut_return_nested_triples_{finite,rational,infinite}_yes` | Exact nested parse and concrete constructor/triple acceptance | Canonical cut termination in the respective domain |
| `lp_cut_seg_{finite,rational,infinite}_yes` | Exact segment parse and `check_lpc_seg_certificate_xml` acceptance | Canonical cut termination in the respective domain |
| `lp_cut_projected_{finite,rational,infinite}_yes` | Exact projected parse and `check_lpc_projected_xml` acceptance | Canonical cut termination in the respective domain |
| `lp_cut_mgu_finite_yes` / `lp_cut_mgu_rational_yes` / `lp_cut_mgu_infinite_yes` | Exact MGU constructor parse result and `check_lpc_mgu_constructor_xml` acceptance | Canonical cut termination in the respective domain |
| `lp_cut_constructor_finite_yes` / `lp_cut_constructor_rational_yes` / `lp_cut_constructor_infinite_yes` | Exact constructor parse result and `check_lpc_constructor_xml` acceptance | Canonical cut termination in the respective domain |
| `lp_cut_source_finite_no` / `lp_cut_source_rational_no` / `lp_cut_source_infinite_no` | Exact source-NO parse result and `check_lpc_no_xml` acceptance | Negation of canonical cut termination in the respective domain |

These are not assumptions that a processor is sound or that two semantics agree.
They identify the actual input and acceptance event. The ITS abstract theorem
also covers general LTSs; singleton entrypoint validity is exposed separately by
`its_translate_finite`. No standalone source parser correctness theorem is claimed.

The bridge dependency audits reject admitted proofs and unexpected oracle names.
ITS inherits `Regexp_Method.check_eqv`; the pure-LP and cut-table YES bridges
also inherit `Types_To_Sets.cancel_type_definition`. These existing Isabelle
mechanisms remain in the trust surface for those serialized YES corollaries.
All seven pure-LP NO corollaries and the three cut source-NO corollaries have no oracle dependencies. The separate cut
domain/factorization audit reports no oracle dependencies. The remaining trust
surface includes the kernel, extracted arithmetic/checking code,
compiler/runtime and original-input binding. Arithmetic guard predicates in
`ITS_Spec` acquire their meaning through the native arithmetic interpretation;
reviewing the relational execution definition alone does not review that evaluator.

All seven pure-LP NO endpoints now have canonical corollaries for all three
domains, including accelerated pattern loops. The [complete NO receipt](data/lp-no-all-bridges-20261110.json)
records the finite witness proofs, universal-MGU lifting and combined oracle-free audit.
No nontermination transfer from an arbitrary-unifier overapproximation is assumed.

Ferrum's `prove-lp` and `prove-lp-cut` select finite terms by default;
`--semantics rational-trees` and `--semantics infinite-trees` select the separate
properties. Complete source identities and reconstructed certificate subjects
include the selected domain. The certificate formats remain unchanged: each
covered accepting family has a separate soundness theorem for each domain.
The runtime binds the original program and query to the certificate and requires
the exact checker verdict for the chosen category and polarity. Internal residual
proofs retain their stronger native relation; an exact-domain claim alone cannot
discharge such a residual. Historical diagnostic probes keep their rational-tree
context and label it explicitly. See the [runtime boundary review](../../ferrum/docs/its-lp-category-boundary.md).

For all 16 cut YES endpoints and the source-NO endpoint there is no remaining
assumed soundness, semantic equivalence, MGU property or domain closure premise.
The finite/rational locale instances discharge all algebraic premises. Parse
results and checker acceptance are concrete input conditions, not mathematical
assumptions about the checker. This establishes soundness, not completeness:
for example, the NO checker can require failure even over unrestricted trees,
which is stronger than finite-domain failure and can limit certificate coverage.

No semantic obligation is introduced as an axiom, admission, or caller-supplied
assumption. The [completion ledger](its-lp-completion.md) distinguishes checked
mathematics from runtime integration evidence and the remaining trust surface. Production binaries, certificate formats and generated checker logic have not
been changed. Ferrum source parsing now rejects multiple ITS entrypoint
declarations; see its [boundary review](../../ferrum/docs/its-lp-category-boundary.md).

## Verification

Use `make isabelle-category-specifications` for the HOL-only definition package,
`make isabelle-category-properties` for examples and derived properties, and
`make isabelle-its-category-bridge` / `make isabelle-lp-category-bridge` for the
separate checker sessions. The latter need the existing IsaFoR/AFP environment.
Bridge ROOTS do not select the whole repository for rebuilding.

Build logs, including failed intermediate proof attempts, are retained under
`target/its-lp-specifications`. The package guard rejects proof commands, external
imports and external README links in the specification directory. Documentation
conformance is checked independently of Isabelle.

The initial [verification receipt](data/its-lp-specifications-20261110.json) preserves the earlier partial state and pins the
source hashes, successful checks, inherited oracle names and unfinished work.

The [cut follow-up receipt](data/lp-cut-review-20261110.json) records the resolved
competition policy, the unrestricted-tree cut-table YES bridge, auxiliary domain
proofs, successful build logs and the remaining finite-term obligations. It does
not replace or rewrite the earlier receipt.

The [domain-bridge receipt](data/lp-cut-domain-bridges-20261110.json) records the
completed finite/rational table-YES and all three source-NO connections, the
checked pumping example, exact source hashes and theorem oracle audits. It
preserves the earlier partial receipts and lists the uncovered dispatcher
families and original-input obligations explicitly.

The [completion ledger](its-lp-completion.md) records closure of the proof and
focused runtime requirements, with the [final receipt](data/its-lp-completion-20261110.json).
It keeps parser/compiler trust and coverage limitations explicit.

The [composition receipt](data/lp-cut-composition-bridges-20261110.json) records all twelve composed/nested corollaries. Continuation-domain membership is proved from actual returned environments; residual reachability alone is not used to assume that membership.

The [projected receipt](data/lp-cut-projected-bridge-20261110.json) records the three projected-return corollaries. It does not cover the separate projected segment endpoint.

The [segment receipt](data/lp-cut-segment-bridge-20261110.json) records the earlier basic segment milestone. The [complete cut-family receipt](data/lp-cut-all-checkers-20261110.json) adds free/projected/triple segments and audits all 51 canonical corollaries across the 17 actual dispatcher branches.
