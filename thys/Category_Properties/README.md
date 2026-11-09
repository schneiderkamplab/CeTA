# Properties and examples of the rewriting specifications

This package proves facts about the sibling `Category_Specifications` package.
It depends only on that package and HOL. It contains the infinite-sequence
characterizations of nontermination, structural preservation lemmas, the
operational-to-ordinary Conditional implication, and proved category examples.

The `*_Properties.thy` files correspond to the definition theories. Shared
sequence results live in `Rewriting_Sequences_Properties.thy`; shared
first-order results live in `TRS_Properties.thy`. `*_Examples.thy` contains
illustrations and their proofs, including edge cases. These files are not part
of the mathematical definition of a category.

`Higher_Order_Properties.thy` also defines the ambient, unrestricted-sort
termination predicate used in representation proofs. The category's canonical
predicate is `higher_order_terminates_over_sorts`, defined in the specification
package. The ambient predicate is a proof abstraction, not a second input category.

```sh
isabelle build -D /path/to/Category_Properties
```

The relative `ROOTS` entry discovers the sibling specifications. No checker,
IsaFoR representation or generated code is imported.
