# Layered Isabelle builds

The proof checker is split into persistent Isabelle heaps so that CSR
development does not rebuild the complete checker after every edit.

| Target | Contents | Use |
| --- | --- | --- |
| `Proof_Checker_Base` | Generic termination checker | Stable dependency heap |
| `CSR_Checker_Base` | Stable CSR definitions and soundness lemmas | Rebuild after foundational CSR changes |
| `CSR_Checker_Core` | CSR proof driver and recursive graph checking | Default target while editing CSR processors |
| `CSR_Checker_Extensions` | Minimal, improved, and conservative CSDP theories | Validate CSR extension changes |
| `Proof_Checker` | Parsers, verifier, and complete checker | Final certification gate |

Use the same Isabelle options between builds because options are part of the
heap identity. For this workspace:

```sh
export AFP=/work/dfm/festschrift/ferrum/.tools/afp-current/thys
export ISABELLE=/work/dfm/festschrift/ferrum/.tools/Isabelle2025-2/bin/isabelle

make isabelle-csr-core
make isabelle-csr-extensions
make isabelle-proof-checker
```

`ISABELLE_JOBS` defaults to 16 and can be overridden. The core target is the
normal edit/test loop. Run the full checker before exporting generated code or
claiming certification.

Measured on 2026-07-26 after warming the dependency heaps:

- `CSR_Checker_Core`: 39 seconds with standard options.
- `CSR_Checker_Extensions`: 13 seconds with the core cached.
- `Proof_Checker`: 3 minutes 7 seconds for the full production gate.

## Temporary feature layers

For a new checker feature, do not iterate through `Proof_Checker` and `Code`.
Create a temporary `ROOT` under `target/` with three uniquely named sessions:

1. an extension-baseline session containing the unchanged extension theories;
2. a semantic child session containing only the new definitions and soundness
   theorem;
3. an executable child session containing the processor/checker adapter.

Build these sessions with a dedicated `ISABELLE_IDENTIFIER` and identical
thread/options settings.  Edits to executable plumbing then reuse both cached
parent heaps, while edits to the semantic theorem avoid rebuilding parsers and
code generation.  Never run two builds that write the same identifier.  Once
both temporary children pass, move the theories into the production session
and run the final gates exactly once:

```sh
isabelle build -d thys CSR_Checker_Extensions
isabelle build -d thys Proof_Checker Code
isabelle export -n -x 'Code.Code_Haskell:**' -O target/feature-export \
  -d "$AFP" -d thys Code
make haskell
```

The production checker and generated Haskell must always come from that final
production build, never directly from a temporary development heap.

## Relative ADP graph layer

Relative ADP graph semantics live in the thin
`Relative_ADP_Dependency_Graph_Dev` session. Its generic finite-branching
argument is isolated in `Finite_Branching_Dichotomy.thy`; the ADP-specific
selection, origin, and labeling lemmas remain in
`Relative_ADP_Dependency_Graph.thy`.

During development, load the stable `Relative_ADP_Processors_Dev` parent once
in a dedicated Isabelle console and replay renamed copies of these two theories
from `target/adp-console-flat`. This gives sub-second theory checking after the
parent is resident and avoids rebuilding any CSR, parser, or code-generation
heap. The 2026-08-11 selected-origin checkpoint was replayed as
`Draft.Finite_Branching_Dichotomy_Test5` and
`Draft.Relative_ADP_Dependency_Graph_Test38`.

The selected application is semantically significant: strict chain indices
prefer a sharp main-ADP witness, and origin edges pin the chosen ADP and redex
position. Do not replace this by the union of all witnesses for a term
transition when proving dependency labels. Such a union is adequate for marker
reachability but can mix incompatible applications in the graph-label bridge.

The next 2026-08-11 checkpoint was replayed as
`Draft.Relative_ADP_Dependency_Graph_Test56`. For every selected canonical
origin away from the applied redex, it now proves the precise alternative
needed by the graph bridge: either the origin is preserved above or parallel
to the redex, or the erased tracked projection is identical after the step.
The variable-transport case is proved directly from the valid VRF and the
substitution positions; it does not assume that source and target positions
are different. The corresponding selected unlabeled moving-edge theorem then
gives equality of the root-marked projections.

The 2026-08-11 dependency-edge checkpoint was replayed as
`Draft.Relative_ADP_Dependency_Graph_Test74` from the same warm parent heap in
2.44 seconds. It strengthens the moving-edge result to every unlabeled edge:
rewrites parallel to or below the tracked marker preserve its root-marked
projection, while a rewrite strictly below it is simulated by one weak step
over the erased ADPs. The simulation composes over arbitrary unlabeled origin
paths. Labeled source and target projections are then reconstructed as
instances of the selected ADP left-hand side and annotated right-hand-side
subterm, respectively. Consequently, a labeled edge followed by an unlabeled
segment to the next label is a genuine `relative_adp_dependency_edge`.

The proof deliberately uses the existing `replace_at_append_context` law for
nested replacement. A broad simplifier call at this point diverged; retaining
the explicit law keeps the replay deterministic and avoids accidental changes
to graph estimation or origin semantics.

The 2026-08-11 fixed-witness checkpoint was replayed as
`Draft.Relative_ADP_Dependency_Graph_Test99`. The selected application now
projects from a full step witness containing the ADP, redex, substitution,
VRF, and generated annotation set. Selected origin edges are restricted to
that exact witness. This follows the canonical-origin construction in the
relative-ADP dependency-graph proof and prevents an existential union from
combining incompatible VRFs for the same term transition.

The same checkpoint proves that the fixed witness supplies an origin
predecessor for every target annotation. It also proves that an origin source
away from the applied redex has exactly one successor: distinct variable
positions in a left-hand side are parallel, whereas two decompositions of the
same source position force them to be comparable. Therefore every offshoot of
the selected heavy path starts at a labeled ADP application. This is the local
branching fact needed for the minimal-lasso half of Theorem 33; the remaining
work identifies late offshoot labels as base ADPs with multiple annotations
and lifts the infinite path to the finite estimated dependency graph.

The 2026-08-11 finite-graph checkpoint was replayed as
`Draft.Finite_Branching_Dichotomy_Test14` and
`Draft.Relative_ADP_Dependency_Graph_Test125`; the latter completed in 3.28
seconds in the warm console. The generic layer now enumerates infinitely many
events on a path, proves that the intervals between consecutive events contain
only non-events, and extracts an eventual mutual-reachability class from every
infinite path over a finite node set.

The ADP layer specializes this construction to selected labels. Consecutive
labels on the canonical origin path induce genuine semantic dependency edges,
and every label belongs to the finite ADP problem. Reachability is explicitly
restricted to graph nodes in that problem; paths through arbitrary external
terms are not admitted. The resulting component is the maximal
mutual-reachability class of its anchor, is pairwise connected, and contains a
main ADP whenever the origin path has infinitely many main events. This
finishes the main-containing SCC half of the soundness argument for Theorem 33.
The remaining semantic step is the minimal-lasso half: after main events cease,
project the recurring branching base labels in the graph over flattened main
ADPs plus base ADPs, and project one offshoot to its first main label.

The next lasso-core checkpoint was replayed as
`Draft.Finite_Branching_Dichotomy_Test15` and
`Draft.Relative_ADP_Dependency_Graph_Test131`. It proves that infinitely many
offshoots with only finitely many main events induce infinitely many selected
base labels whose ADPs have at least two distinct annotations. After discarding
the finite prefix, their label stream lies in the graph problem
`flat(P) union B`. Dependency edges transport to this graph because its erased
rule set is exactly the erased rule set of `P union B`. Finite recurrence then
produces a maximal mutually reachable component containing a branching base
ADP, which is the SCC premise of a minimal lasso in Definition 32 of the IJCAR
2024 relative-ADP paper. The remaining lasso obligation is to project a chosen
origin offshoot to the first main label and thereby obtain the finite lasso
stem. No executable checker or production CeTA integration should be enabled
until that stem theorem and the resulting full processor theorem are proved.

The finite stem bridge was then replayed as
`Draft.Finite_Branching_Dichotomy_Test18` and
`Draft.Relative_ADP_Dependency_Graph_Test135`. A generic event-compression
theorem decomposes every finite path between labeled nodes into labeled-edge
plus unlabeled-tail segments. The existing ADP segment theorem maps each one
to a dependency edge, so every finite selected-origin path between labels maps
to dependency-graph reachability. Applied to an offshoot, this produces a path
from the branching base ADP in the recurring component to a main ADP. Thus the
semantic lasso witness now has all substantive Definition 32 ingredients:
the base-graph SCC, a base ADP with more than one annotation, and a finite stem
to a main ADP. The executable layer may choose the first main node on that
finite stem to obtain the required minimal representative.

The first executable graph checkpoint was replayed as
`Draft.Relative_ADP_Dependency_Graph_Test148`. It defines the checker-owned
list of annotated right-hand-side candidates, a conservative `tcap` edge
test, indexed successor lists, and an executable test for base ADPs with more
than one annotation. Isabelle proves that every semantic relative-ADP
dependency edge is present in this estimated graph and that the branching
test is exactly Definition 32's branching predicate. The full theory replayed
in 4.22 seconds from the warm child session. These functions are not yet
exposed through XML or `Certified`: the remaining processor theorem must
first prove that selective removal of annotations outside the checked SCC or
lasso preserves the required infinite child chain.

The local graph-child projection checkpoint was replayed as
`Draft.Relative_ADP_Dependency_Graph_Test166`. For every parent ADP step and
every projected source with the same erased term, it constructs a child step
over `Q union flat(A - Q)` whose target has the same erased term as the parent
target. Crucially, flattened outside-`Q` ADPs retain the original valid
variable-reposition function: only their rule annotations are removed. An
earlier empty-VRF draft would have lost annotations transported through
variables and was rejected before checker integration. The theory also proves
that validity of a VRF is preserved by full ADP annotation erasure. The next
bridge specializes this construction to the selected fixed witness and proves
that every retained origin marker remains retained in the projected target.

The fixed-witness projection and chain checkpoint was replayed as
`Draft.Relative_ADP_Dependency_Graph_Test175`; the complete theory checked in
5.35 seconds in the warm child session. The executable projected witness
retains the parent substitution and VRF, recomputes annotations from its
projected source, and flattens exactly the pairs outside `Q`. Isabelle proves
that this witness is a valid step of `Q union flat(A - Q)` and has the same
erased target as the parent witness. It also proves the key origin invariant:
a marked origin survives when its applied ADP lies in `Q`, or when the origin
is not the applied redex (the latter excludes exactly the root-target case
destroyed by flattening). Primitive recursion then builds the projected child
chain and proves erased-term equality, a valid child step at every index, and
inductive preservation of a chosen origin path. The remaining semantic task
is to extract infinitely many strict child steps for each checked main SCC or
minimal-lasso child and package that result as the graph processor theorem.

The strict-chain checkpoint was replayed as
`Draft.Relative_ADP_Dependency_Graph_Test178` in 5.45 seconds. Whenever the
tracked origin is the redex of a selected main ADP in `Q`, the projected
witness is a strict step of `P intersection Q`. Isabelle lifts infinitely many
such events to an explicit `ideriv` over the graph child and proves that child
ADP problem nonterminating. This establishes the contrapositive semantic core
of recursive graph decomposition. What remains is finite-graph selection:
specialize the generic chain theorem to the eventual main component and to a
recurring minimal lasso, then validate that the executable certificate lists
all children required by that dichotomy.

The eventual-main-component checkpoint was replayed as
`Draft.Relative_ADP_Dependency_Graph_Test191`; the full theory checked in 5.61
seconds. The proof starts at the first enumerated label in the eventual SCC,
shifts the original derivation and fixed selected witnesses by that finite
prefix, and applies the projected-chain theorem. Every subsequent labeled
redex belongs to the SCC by monotonicity of label enumeration. Every
unlabeled origin is away from the selected redex by the previously verified
origin-shape lemma, so flattening its ADP cannot remove the tracked origin.
Infinitely many main events therefore become strict steps in the SCC child.
This completes the semantic main-SCC branch of Theorem 33 without changing or
weakening dependency-graph estimation. The minimal-lasso branch and the
executable certificate coverage theorem remain before XML exposure.

The retained-lasso projection checkpoint was replayed as
`Draft.Relative_ADP_Dependency_Graph_Test204`; the full theory checked in 5.80
seconds. This follows Definition 32 and the soundness proof of Theorem 33 in
the long version of Kassing, Dollase, and Giesl's relative-ADP paper. A
retained origin edge is a selected canonical-origin edge whose source is
unlabeled, or whose applied ADP belongs to the chosen lasso. Isabelle proves
that retained edges preserve annotations in the projected child, first for
one edge and then for every finite retained path.

Consequently, every retained offshoot ending in a main event becomes a strict
step of the child problem. The theorem
`relative_adp_selected_recurring_retained_main_paths_not_SN` packages the
recurring case: an infinite retained base path with infinitely many retained
paths to selected main events induces an explicit infinite projected child
chain with infinitely many strict steps. This closes the term-level
projection argument for a fixed recurring lasso. The remaining semantic
selection step must extract one such finite lasso node set from infinitely
many canonical-origin offshoots. The executable checker must then cover every
possible recurring set; it must not silently restrict this to simple graph
paths unless a separate theorem justifies that restriction.

The finite-family checkpoint was replayed as
`Draft.Relative_ADP_Dependency_Graph_Test205`; the full theory checked in 5.96
seconds. It separates the semantic proof from the eventual graph enumeration.
For any finite family of checked lasso sets, if every late generated main
redex is reachable through at least one retained family member, Isabelle's
finite pigeonhole argument selects one member that recurs infinitely often.
The fixed-lasso theorem then proves that member's child nonterminating. This
is the coverage interface the executable checker must discharge. It permits a
later optimized SCC-DAG enumeration without changing the term-level proof,
while ruling out an under-approximating family that misses cyclic offshoot
stems.

The executable Gabow checkpoint was replayed as
`Draft.Relative_ADP_Dependency_Graph_Impl_Test11`; the child implementation
theory checked in 1.59 seconds against the warm semantic heap. The checker
builds the finite indexed estimated graph, adds reflexive edges solely so that
Gabow's nontrivial-SCC interface also returns isolated vertices, and invokes
IsaFoR's verified `scc_decomp`. Isabelle proves exact SCC characterization,
index bounds, coverage and disjointness, and eventual capture of every
infinite estimated path by one emitted SCC.

A proof-only occurrence index then connects semantic ADP labels to the
executable graph. It is deliberately absent from generated code and handles
duplicate ADPs without assuming list distinctness. The theorem
`relative_adp_selected_estimated_main_scc_child_not_SN` proves that every
nonterminating selected chain with infinitely many main events is captured by
an emitted SCC containing a main ADP, and that the corresponding projected
child is nonterminating. This discharges executable coverage for the main-SCC
branch. The branching-base branch still requires a verified finite family of
SCC-condensation paths that satisfies the previously proved lasso-family
coverage interface.

The executable corridor checkpoint was replayed as
`Draft.Relative_ADP_Dependency_Graph_Impl_Test31`; the expanded child theory
checked in 2.38 seconds in the warm session. IsaFoR's verified work-list
closure now computes forward and reverse reachability in the finite estimated
graph. A corridor is the intersection of nodes reachable from a branching
base pair with nodes from which a chosen main pair is reachable. Isabelle
proves the exact closure equations and lifts every semantic dependency-graph
path, including every intermediate pair, into the executable corridor.

For every SCC of `flat(P) union B`, the generator emits the SCC plus one such
corridor for each branching base pair in the SCC and each reachable main pair.
This is intentionally a corridor rather than an enumeration of simple paths:
it contains cyclic detours inside and between SCCs and therefore cannot miss
an offshoot merely because its finite stem repeats a graph node. The candidate
membership theorem verifies that every guarded SCC/source/target tuple occurs
in the global finite family. The remaining lasso theorem must connect selected
origin offshoots to these candidates and discharge the retained-edge and
coverage premises of `relative_adp_selected_finite_lasso_family_has_non_SN_child`.

That lasso connection is now complete. The generated family combines the
eventual lasso SCC, the full-problem predecessor cone of the branching source,
and its source-to-main corridor. The predecessor cone preserves the selected
chain's finite prefix without shifting the derivation; the eventual SCC keeps
every later base label; and each late offshoot supplies one generated corridor.
Consequently one member of the finite family retains the complete selected
origin path. The complete lasso branch replayed in the warm child session as
`Draft.Relative_ADP_Dependency_Graph_Impl_Test54` in 3.04 seconds.

The executable graph processor emits both main-SCC and lasso candidates. The
contrapositive theorem `relative_adp_estimated_graph_has_non_SN_child` proves
that every nonterminating relative ADP parent has a nonterminating emitted
child, using the formally verified heavy-path main-event/offshoot dichotomy.
`relative_adp_estimated_graph_processor` exposes the direct checker contract:
termination of all emitted children implies termination of the parent. The
combined proof replayed as Test57 in 3.46 seconds, and the final direct theorem
as `Draft.Relative_ADP_Dependency_Graph_Impl_Test58` in 3.51 seconds. The next
step is to expose this finite child family in CPF/CeTA and emit it from Ferrum.

The checker exposure is implemented in the next thin layer. A
`Relative_ADP_Dependency_Graph` proof node carries exactly one recursive proof
per checker-computed candidate. CeTA recomputes the complete ordered candidate
list, checks function-rooted left-hand sides, rejects a child-count mismatch,
constructs each child problem itself, and recursively checks every proof. The
adapter soundness proof applies `relative_adp_estimated_graph_processor`
directly. `Draft.Relative_ADP_Checker_Adapter_Test4` replayed in 14.51 seconds,
the theorem-level checker tests in 0.69 seconds, and the recursive XML/CPF
integration as `Draft.Relative_ADP_Ceta_Test1` in 23.70 seconds. The XML node
is named `relativeAdpDependencyGraph`; its children are nested
`relativeAdpTerminationProof` elements in checker candidate order.

The generated-code replay exposed and removed three non-executable remnants:
sharp-position tests now inspect term roots directly, main-SCC overlap uses
list membership, and lasso component membership uses a mapped list instead of
a finite set. The complete candidate list is normalized with `remdups`; this
preserves the candidate set used by the soundness theorem while avoiding
duplicate recursive checker obligations. The final executable theory replayed
as `Draft.Relative_ADP_Dependency_Graph_Impl_Test64`, and the checker/parser
layers replayed as Tests 9 and 6. `Draft.Relative_ADP_Code_Haskell_Test7`
generated the verified Haskell checker in 226.94 seconds.

The extracted checker was compiled and applied to Ferrum's retained
`TRS_Relative/Relative_05/rt1-3.ari` graph certificate. It independently
reconstructed two graph children and returned `CERTIFIED`. An earlier
five-child certificate is rejected with a child-count mismatch, confirming
that Ferrum cannot choose a smaller graph than the verified estimator.

## Production relative-ADP Com verifier rebuild (2026-08-12)

The production verifier was rebuilt from branch
`codex/relative-adp-20260811` in the isolated Isabelle home
`target/isabelle-home-com-production-20260812`, with identifier
`codex_ex1_layer_20260803`. Existing verified dependency heaps through
`Relative_ADP_Derelatification_Dev` were hard-linked from the earlier isolated
home; all Com, checker, integration, generated-code, and native-binary outputs
were rebuilt.

The semantic build exposed a pathological `blast` invocation in a
reflexive-transitive-closure induction. It searched for 1848 seconds because
the proof referenced the accumulated closure instead of the new edge. The
proof now uses the induction rule's edge and induction-hypothesis facts
directly. The production replay also made position-list distinctness,
multiset-count reasoning, and fresh-component map congruence explicit. With
those changes, `Relative_ADP_Com_Reduction_Pair_Dev` checked in 45 seconds
wall time, including 16.7 seconds for the theory itself.

The checker replay aligned the synthetic Com-law variables with IsaFoR's
`string` type and includes the law rules in the same weak rule list passed to
`rel_impl_mono_redpair`. Thus the standard verified reduction-pair theorem,
not an extra unchecked inference, yields their inclusion in the weak order.
Executable `ceq`, `ccompare`, and red-black-tree `set_impl` instances are
derived for both ADP symbol wrappers. `Relative_ADP_Checker_Dev`, including
its theorem-level tests, checked in 51 seconds.

The unified `Relative_ADP_Ceta_Dev` integration replayed the production
`Proof_Checker`, relative CPF parser, and Haskell export in 9 minutes 18
seconds. The Haskell export took 250 seconds. This terminal export session
does not retain its own heap unless another session depends on it; its durable
outputs are `generated/Haskell/Ceta_Relative.hs` and the native checker.
`make -j 16 ceta-relative-adp` compiled the 16 MiB `ceta` executable in 3
minutes 20 seconds. `make test-relative-adp` passed.

After integration into the main CeTA-CSR worktree, the Relative-ADP executable
was made command-line compatible with the ordinary CeTA executable.  Besides
whole certificates, it accepts `--inputf`, `--propertyf`, `--property`,
`--answerf`, `--answer`, `--allow-assumptions`, and `--version`; unsupported
Relative-ADP syntax still falls back to the established unified checker.
`make test-relative-adp` and Ferrum's complete 690-test Rust library suite pass
with this executable, including every CSR fragment/checker integration test.

The real Ferrum certificate
`ferrum-relative/target/relative-adp-com-certified-smoke/rt2-2-com.cpf.xml`
was accepted with exit status 0 and output `CERTIFIED`. A well-formed mutation
that changes the first `adpCom2` interpretation from `x1 + x2` to `x1 + 0`
was rejected with exit status 1 and a monotonicity error. Full replay outputs,
statuses, mutated CPF, and SHA-256 hashes are retained under
`target/production-verifier-rebuild-20260812`. The rebuilt binary hash is
`4a8175dcf85748ab44557429c0c57c3c18b89f77cd442c6f515850ecf8b8c1b3`.
The semantic, checker, and integration sources contain no `sorry`,
axiomatization, or oracle declaration.
