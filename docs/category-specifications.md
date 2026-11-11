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


## Reusing the local verification cache

The established cache for this checkout uses 64-bit Poly/ML, the Isabelle
installation under `../ferrum/.tools/Isabelle2025-2`, and the consolidated AFP
snapshot. The user settings in `target/trs-standard/user` select
`/tmp/trs-standard-output` for output heaps and `/tmp/trs-standard-heaps` for
system heaps. These temporary caches are local build artifacts, not prerequisites
for using the specification package elsewhere.

From the CeTA repository, reproduce the cached bridge build with:

```sh
USER_HOME="$PWD/target/trs-standard/user" \
ISABELLE_IDENTIFIER=trs_standard \
AFP="$PWD/../CeTA-consolidated/target/consolidation-build/afp-source/thys" \
../ferrum/.tools/Isabelle2025-2/bin/isabelle build -j4 \
  -d ../CeTA-consolidated/target/consolidation-build/afp-source/thys \
  -d thys -D thys/Category_Bridges
```

Use the same environment with `isabelle getenv ISABELLE_HOME_USER
ISABELLE_HEAPS ISABELLE_HEAPS_SYSTEM ML_PLATFORM AFP` to inspect the effective
configuration before a build. An absent cache requires a rebuild; do not copy
heaps between the 32-bit and 64-bit Poly/ML platforms or bypass Isabelle's
source/dependency checks. Selecting the entire bridge directory includes the
serial LP-with-cut session chain, which must rebuild when shared term syntax
changes. The narrower make targets above remain available for category-local
changes.

The [November 11 cleanup verification](data/spec-syntax-cleanup-20261111.json)
records a successful complete cached bridge build in 14 minutes 46 seconds,
including the LP-with-cut chain, with no source-registration errors. All ten
former shared-base declarations are unchanged modulo whitespace after moving
the raw syntax into its own theory. The
[build log](data/spec-syntax-cleanup-20261111-build.log.gz) preserves the session
results. Generated checker code and production executables were not changed.
An unchanged-build dry check then passed in 28 seconds with no rebuilds required.
