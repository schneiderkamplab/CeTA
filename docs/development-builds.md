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
