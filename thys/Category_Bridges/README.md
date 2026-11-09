# Rewriting representation and checker bridges

This package connects the sibling specifications and properties to IsaFoR and
CeTA. It is deliberately outside the self-contained definition package.

`Bridge/TRS_Representation.thy` owns the shared first-order term, rule,
substitution, signature and context translations and step correspondence.
`Bridge/Rewriting_Sequence_Equivalence.thy` supplies generic sequence and
termination transfer without importing Standard's category equivalence.
Individual equivalence theories specialize these results. SRS uses word and
unary encodings; Higher-order has a separate typed representation.

Mathematical CSR signature extension lives in `Bridge/CSR_Signature_Extension.thy`.
Its import graph does not include the integrated CPF dispatcher. Concrete CSR
checker soundness composes it in `Context_Sensitive_Integrated`.

`Common_Integrated/Category_Integrated_Base.thy` extracts semantic acceptance
from an exact parsed certificate and serialized acceptance. Category-specific
integrated theories retain explicit input/configuration and YES/NO conclusions.
Their admission and oracle audits remain beside the theorems they audit.
The older generic checker bridges are valid reusable results with explicit
module contracts; the concrete integrated theorems discharge those contracts.

The existing category-specific checker session names and make targets remain
available. `Category_Integrated_Base` is their shared CPF parent. The
Higher-order sessions retain their separate native checker dependency chain.

```sh
isabelle build -d /path/to/AFP/thys -d /path/to/CeTA/thys -D /path/to/Category_Bridges
```

Checker-family restrictions and signature-transfer conditions belong here,
not in the category definitions. The specification does not import this package.
