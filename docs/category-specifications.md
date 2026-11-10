---
type: Formal Specification
title: "Rewriting category specification package"
status: stable
---
# Rewriting category specification package

The [self-contained specification package](../thys/Category_Specifications/README.md)
contains only mathematical definitions and their explanations. It depends on
Isabelle/HOL, and can be copied and built without IsaFoR, CeTA, or either of the
other packages below. The package's own reading guide covers every category,
its validity predicate, and its final termination predicate.

| Package | Contents | Dependency direction |
| --- | --- | --- |
| [Category_Specifications](../thys/Category_Specifications/ROOT) | Shared vocabulary and category definitions | HOL only |
| [Category_Properties](../thys/Category_Properties/ROOT) | Derived properties, nontermination characterizations and proved examples | Specifications only |
| [Category_Bridges](../thys/Category_Bridges/ROOTS) | IsaFoR representations, equivalences, checker connections and audits | Specifications/properties and the existing libraries |

First-order categories share `fo_term`, `fo_subst`, `fo_context`, `fo_plug`,
`trs_problem` and `fo_step`. SRS shares its word definitions; Higher-order shares
its typed, binding-aware syntax. All rewriting categories use `no_infinite_steps`.
Definitions do not import theorems or checker code. The former `standard_*`
shared names were made category-neutral; the category-specific
`trs_standard_terminates` name remains unchanged.

The [ITS and LP extension review](its-lp-specifications.md) records the newer
definitions and their separately audited bridge coverage. That extension is
still a draft: pure-LP NO and cut checker correspondence remain open.

Read the specification first. Then consult the corresponding properties and
examples, followed by the [category review register](category-assumptions-review.md)
for exact equivalence/checker statements, coverage and trust boundaries.
[Earlier build and replay milestones](category-specification-verification-history.md)
are preserved separately from this current reading guide.

```sh
make isabelle-category-specifications ISABELLE=/path/to/isabelle
make isabelle-category-properties ISABELLE=/path/to/isabelle
make isabelle-category-specification-bridges ISABELLE=/path/to/isabelle AFP="$AFP"
python3 scripts/check_category_package.py
python3 scripts/check_okf.py docs
```

The category-specific integrated make targets and existing checker session names
remain available. Their theories now live under `Category_Bridges`, outside the
specification package. Historical receipts retain their original source paths
and hashes; they describe the revisions at which they were recorded.

Reviewing the definitions establishes the intended question. Equivalence and
soundness proofs establish what accepted certificates mean. Neither establishes
checker completeness, parser correctness, or compiled executable correspondence.

The [package refactor verification receipt](data/specification-package-cleanup-20261109.json)
records the source hashes and build evidence. A copied specification directory
built in an isolated Isabelle user home without AFP or sibling-package paths;
the properties and all bridge/checker sessions also built. A mechanical comparison
covered all 78 original definitions, allowing only the shared-name changes and
unfolding of the common sequence definition. No generated checker or runtime
artifact changed.
