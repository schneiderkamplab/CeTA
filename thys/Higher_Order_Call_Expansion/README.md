# Source-bound higher-order call expansion

This session extends the higher-order computability closure. It does not
replace the source rewrite system with a normalized system.

The exported `ho_check_expansion_input_sound` theorem proves
`wf ((ho_relation S V R A)⁻¹)` for the supplied **original** signature and rules.
The CLI reconstructs those from the input independently of proof synthesis.

## Checked composition

- `Higher_Order_Spine_Expansion`: beta expansion at a fully applied,
  base-typed lambda spine. All arguments must be strongly normalizing; the
  full contractum must be computable. Body and argument reductions are covered.
- `Higher_Order_Definition_Expansion` and `Higher_Order_Definition_Check`:
  constant-call expansion into a closed lambda. Every source rule at every
  applicable prefix must be simulated, not just a preferred definition.
  Positively accessible arguments must additionally be computable.
- `Higher_Order_Beta_Instances`: head-beta simulations survive typed
  substitution, including binder lifting.
- `Higher_Order_Expansion_Closure`: fuel-bounded composition of expansion,
  application, existing closure leaves, and a separately justified extension.
- `Higher_Order_Expansion_Recursive`: recursive calls whose arguments may
  themselves use expansion. The existing checked strict semantic call order
  remains mandatory.
- `Higher_Order_Expansion_Semantic` and `Higher_Order_Expansion_Schema`:
  connection to weak polynomial interpretations and whole-system termination.

A functional argument's strong normalization can be established by checking
one well-typed full application as computable, then reflecting normalization
through application subterms. This **does not** infer computability of the
functional argument. `Higher_Order_Expansion_Observations` proposes such
applications by type; proposals have no trusted status.

The synthesis implementation derives pure combinators from live source rules
and synthesizes order parameters with SMT. It contains no benchmark-name
dispatch or supplied orders. Arbitrary definitions in a certificate still
have to pass the executable definition checker.

## Build and diagnostics

Use `scripts/check_higher_order_call_expansion.sh` with a private
`HO_ISABELLE_USER_HOME` and `HO_ISABELLE_IDENTIFIER`. The parent is
`Higher_Order_Guarded`; its existing checked dependencies are reused.
`scripts/build_higher_order_call_expansion_checker.sh NEW_DIRECTORY` exports
and compiles the complete checker. No shared heaps are overwritten.

`scripts/Higher_Order_Expansion_Diagnostic.hs` is a non-accepting diagnostic
driver. Its Boolean vector reports the two interpretation-signature checks,
then each weak rule check, then each closure check. Only the ordinary
certification driver may produce a certification result.
