# Relative annotated dependency pairs

Production theories are organized into three layers:

- `Semantics`: annotated terms, chain criteria, dependency graphs,
  derelatification and the separate Com reduction-pair criterion.
- `Checker`: executable list representations, certificate checking and proofs
  connecting the checks to the semantic criteria.
- `Integration`: CPF parsing, CeTA integration and the relative Haskell export.

`Checker/Dependency_Pair_Injective_Renaming.thy` contains the general Q-normal-form
and nonminimal dependency-pair renaming facts. It imports only the framework
implementation. The adapter retains qualified compatibility theorem aliases.
The finite-DP result still requires injectivity and the stated nonminimal,
empty-strict-rule/weak-pair shape; it does not establish a minimal-chain variant.

Existing `_Dev` session names remain compatibility identifiers. The old
`dev/Relative_ADP_Dev` build directories contain only `ROOTS` forwarding files;
production theory sources live here. New builds can register all relative sessions
with `isabelle build -d thys -d thys/Relative_ADP Relative_ADP_Ceta_Dev`.

`Relative_ADP_Checker_Tests` includes formal residual and rejection checks.
These and `examples/relative_adp_rt1_3.cpf.xml` are focused fixtures, not genuine
witness-free replay evidence. The missing ADP replay coverage remains a gap.
