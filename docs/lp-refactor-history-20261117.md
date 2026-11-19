---
type: Verification Record
title: "LP refactor historical checkpoints, 2026-11-17"
status: draft
---
# Historical LP refactor checkpoints

The following records intermediate states, not current outstanding obligations.
See the [current review](its-lp-specifications.md) for completion evidence.

## Intermediate checkpoints

The installed specification now uses polymorphic variables, explicit arities,
`LAtom` predicate applications, and a single-substitution global MGU.
`logic_mgu D a b s` requires every domain-correct unifier to factor through `s`
on every variable. Pure and cut resolution explicitly rename clauses away from
the active goals, then substitute into the renamed body and continuation.
Saved cut alternatives retain their own bindings. `logic_eval` is only shorthand
for substitution after finite embedding. All term-domain wrappers now take the
arity function explicitly.

The [installed-semantics checkpoint](data/lp-installed-semantics-20261117.json)
records passing actual specification and property sessions after this migration.
An isolated proof check of byte-identical copies of the installed pure
representation, raw-symbol YES theorem, and cut structural representation also
passes. This is not yet a complete registered bridge-session build.
Examples cover overloaded predicate names, malformed atom/query arities,
nonground modes, finite versus rational occurs-check behavior, cut scope,
success backtracking and meta-calls. The separate
[ranked-MGU properties](../thys/Category_Properties/LP_Ranked_MGU_Properties.thy)
prove preservation and reflection under the name/arity encoding, including
predicate tags. [Arity projection](../thys/Category_Properties/LP_Arity_Projection.thy)
proves a signature-correct unifier exists whenever a domain-correct unifier does
for well-formed equations and a projection-closed domain. Projection preserves
finite and rational trees. This is not a termination-restriction assumption.

The [fresh-cut correspondence checkpoint](data/lp-fresh-cut-correspondence-20261117.json)
adds passing proofs for the arity invariant along cut runs, global MGU transport
through a bijective runtime representation, and infinite-tree cut execution
correspondence, including failed unification and backtracking. The infinite-tree
table YES corollary also compiles. The registered `Category_LP_Bridge` and
`Category_LP_Cut_Domain_Bridge` sessions pass. The corollary requires explicit source validity; the
proof does not treat an empty execution of a malformed program as validation.

The registered `Category_LP_Cut_Checker_Bridge` session now also passes:
finite and rational table YES corollaries discharge the domain and projection
obligations, while requiring explicit source validity. The new
[MGU arity properties](../thys/Category_Properties/LP_Arity_MGU_Properties.thy)
prove that an MGU with an arity-correct unifier as an instance is itself
arity-correct, and that projection supplies arity-correct factors. These proofs
work for polymorphic variable types and add no variable-supply assumption.

The [pure-LP ranked-boundary checkpoint](data/lp-pure-ranked-20261117.json)
now connects the concrete native program to `logic_rank_program P`, with
arity `snd` and query symbol `(q,length modes)`. Encoding gives source validity
without a signature-restriction hypothesis. The native program and serialized
certificate are unchanged. The registered base, pure-NO and advanced-NO sessions
pass. All seven NO endpoints use explicit freshening and a single global MGU;
their combined audit reports no oracle dependencies. The ranked TOCL09 YES
endpoint and the ten additional YES families also pass (the latter in an
isolated check of the installed theory while its mixed cut-family session is
still being migrated).

**The checker-bridge migration is not complete.** Cut precise-MGU correspondence,
ranked cut YES translations, and the concrete ranked cut parser/checker boundary still
need verification and a full rebuild. The XML cut atom parser accepts a general
term; successful parsing alone is not an ordinary-predicate shape proof. The
reverse representation now has verified inverse laws for explicit user-headed
atom shapes. The [atom-shape checkpoint](data/lp-cut-atom-shape-20261117.json)
proves that native witness steps preserve these shapes, including meta-call
lowering, substitution and backtracking. This is a representation invariant,
not yet the complete arity-aware execution correspondence.
The [fresh-resolution checkpoint](data/lp-cut-fresh-representation-20261117.json)
proves variable-set and freshening correspondence, global-MGU transport,
arity-correct resolution, and backtracking. These lemmas have no oracle
dependencies or admitted proofs. The backtracking lemma explicitly requires an
infinite variable type and finite variable sets in active terms; the concrete
certificate integration must establish those reachable-state conditions.
The [finite-witness checkpoint](data/lp-cut-finite-witness-20261117.json) now
extracts an infinite native run containing only finite terms from accepted NO
certificates. The proof-only witness relation retains finite substitution images
already supplied by checked solved substitutions, and the existing trace and
pumping proofs compile against it. Finite canonical variable support follows;
this checkpoint also has no oracle dependencies or admitted proofs.
The [inverse-simulation checkpoint](data/lp-cut-inverse-simulation-20261117.json)
now replaces the obsolete two-substitution NO translation. It verifies every
native witness step against the single-MGU canonical semantics, lifts infinite
runs, and obtains a canonical infinite execution from an accepted native NO
certificate under explicit source-shape, source/query-arity and domain-projection
conditions. Its audit reports no oracles or admitted proofs. The ranked input
boundary and public NO corollaries must still discharge those conditions.
The [source-NO and ranked-representation checkpoint](data/lp-cut-source-no-ranked-20261117.json)
connects the existing NO checker to the finite, rational and unrestricted source
properties, with source and witness-query arity conditions still explicit.
All three source corollaries pass the zero-oracle/no-admission audit. The
registered LP bridge session also verifies the cut rank/erase representation,
substitution and domain preservation, and the shared-arity control validator.
These are intermediate results: ranked execution/MGU correspondence and final
boundary validation remain open; the source corollaries are not the requested
assumption-free concrete endpoints.
The [ranked-MGU and execution checkpoint](data/lp-cut-ranked-mgu-execution-20261117.json)
now passes in the registered `Category_LP_Bridge` session. It transports global
MGUs through the ranking image and then proves arity restriction for finite,
rational and arbitrary trees. Runtime goal substitution, clause-selection
indexes, cut barriers and pruning, finite/divergent meta-call decoding, variable
sets and freshening are preserved. The audit reports no oracles or admissions.
Whole native certificate-run transport and the final validated boundary remain
open, as does the precise-MGU YES correspondence.
The [ranked cut NO checkpoint](data/lp-cut-ranked-no-20261117.json) now passes
in the complete registered `Category_LP_Cut_NO_Bridge` session. Native resolution,
backtracking, explicit unification and meta-call steps lift to ranked canonical
runs. The finite witness supplies the variable-support invariant; canonical
step preservation propagates arities. Finite, rational and arbitrary-tree NO
corollaries have only parser-result and guarded-acceptance premises, with zero
oracles and no admissions. The pumping-loop example and four boundary examples
also pass.

`check_lpc_ranked_no_xml` is a formal boundary wrapper: it combines the existing
native check with ordinary-predicate shape and fixed-control arity checks on the
program and witness arguments. It preserves overloaded user names. This is not
a claim that the unchanged production executable performs the new guard. The companion
[Ferrum boundary gate](../../ferrum/docs/data/lp-ranked-boundary-20261117.json) now
checks this guard in the existing source-audit path, including NO witness
arguments. The handwritten Rust/XML implementation remains part of the parser
and correspondence trust boundary; the generated checker itself is unchanged. Ranked cut YES and precise-MGU
YES correspondence remain unfinished.
The [ranked forward/table checkpoint](data/lp-cut-ranked-forward-20261117.json)
now passes the registered `Category_LP_Cut_Ranked_Bridge` session. It proves
execution erasure, including fresh resolution, failure, backtracking, explicit
unification and meta-calls, and derives termination transfer. These semantic
proofs have zero oracle dependencies and no admissions. The finite, rational
and arbitrary-tree table-YES corollaries require only the parsed input and
`check_lpc_ranked_table_xml` acceptance; their projection and source-validity
obligations are discharged. The checker dependency audit permits only the two
previously documented inherited oracle mechanisms. Constructor and remaining
YES families, precise-MGU correspondence and the complete downstream rebuild
remain open.

The [ranked constructor/families checkpoint](data/lp-cut-ranked-families-20261117.json)
also passes the registered `Category_LP_Cut_Family_Bridges` session. Constructor
finite, rational and arbitrary-tree YES endpoints now use ranked canonical
semantics and guarded acceptance. The pure-LP YES family endpoints pass in the
same session. Precise-MGU correspondence and its downstream cut families remain
unfinished.

The [arity-MGU extension checkpoint](data/lp-cut-arity-mgu-20261117.json)
passes `Category_LP_Cut_Arity_MGU_Bridge`. For string variables and arity-correct
input atoms, a typed global MGU is an unrestricted global MGU in the finite,
rational or arbitrary-tree domain. The proof names malformed subtrees by
distinct variables and reconstructs them after factorization. Countability of
subtrees supplies the names, including for infinite trees. It requires no
unrestricted-MGU-existence premise and has no oracle dependencies or admissions.
The polymorphic specification remains unchanged; this string specialization
belongs to the checker correspondence layer. Native contextual factorization
and the precise-MGU checker connection still need to be composed with this result.

The [ranked precise-MGU checkpoint](data/lp-cut-ranked-precise-20261117.json)
now passes the complete registered `Category_LP_Cut_MGU_Bridge` session. Typed
MGUs are erased to native global MGUs, clause freshening is preserved, and
native contextual factors cover both the renamed body and caller continuation.
The precise execution and termination-transfer proofs have zero oracle
dependencies and no admissions. The finite, rational and arbitrary-tree MGU-YES
corollaries require only a parser result and `check_lpc_ranked_mgu_xml`
acceptance; all erasure and projection obligations are discharged. The checker
audit permits only the documented inherited oracle mechanisms. The remaining
return, composition, nested, projected and segment endpoints still need migration
and a complete downstream build.

The working tree's complete LP/cut bridge sessions are not yet claimed to pass.

The [global-MGU preparation checkpoint](data/lp-global-mgu-20261117.json) records
the preceding state: its complete old-semantics bridge regression passed in
8m47s, including the LP/cut checker audit. That result is historical and does
not certify the newly installed definitions. It also retains the isolated draft,
examples, rank-MGU equivalence, and pure-LP forward-simulation evidence used
for the migration. The earlier
[polymorphism checkpoint](data/lp-variable-polymorphism-20261117.json) likewise
concerns the previous contextual semantics.

[Variable properties](../thys/Category_Properties/LP_Variables_Properties.thy)
prove fresh renamings for finite sets over infinite variable types, and for
finite lists of rational goals. A singleton type cannot freshen a clause against
a caller using its sole variable. An arbitrary infinite tree can contain every
natural-number variable; infinitude alone is therefore not a sufficient
freshening argument for arbitrary runtime states. Variable-supply requirements
belong in correspondence theorems, with strings at the concrete boundary.

No certificate formats, generated checker code, or production binaries changed.
The package inventory check detects a concurrent, unlisted
`TRS_Conditional_Spec_Base2.thy`, which is untouched. Documentation conformance
passes; the package inventory issue remains separate from LP proof migration.
