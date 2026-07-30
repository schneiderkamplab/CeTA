# Certification Problem Format 4.0

CPF 4.0 is a conservative extension of CPF 3.x. A CPF 3.x certification
problem is also a CPF 4.0 certification problem with the same meaning.
New producers should write:

```xml
<cpfVersion>4.0</cpfVersion>
```

The normative schema is `cpf4.xsd`. Existing CPF 3.x elements and their
semantics are unchanged.

## Context-Sensitive Rewriting

The replacement map remains part of the existing
`input/trsInput/strategy/contextSensitive` element. CSR termination is
termination over terms whose function symbols belong to the finite input
TRS signature.

CPF 4.0 adds these top-level proof elements:

- `csrTerminationProof`
- `csrImprovedDependencyPairs`
- `conservativeCsrTerminationProof`

The first supports CSR rule removal and replacement-map-aware dependency
pairs. Its `csrDpProof` supports empty problems, ordinary DP suffixes,
CSR dependency-graph decomposition, CSR usable rules, CSR subterm
criteria, direct replacement-map-aware LPAR'08 CS instantiation, and CSR
size-change proofs.

The canonical `csrImprovedDependencyPairs` proof implements the exact LPAR'08
construction. It contains an explicit fresh unhiding symbol, the dependency
pairs, and a `csrDpProof`. A checker recomputes ordinary, collapsing,
hidden-term, and exact hiding-projection pairs; the supplied list is not
trusted.

The separate conservative proof contains auxiliary weak rules and retains the
older conservative coverage semantics.

For compatibility with development certificates produced before CPF 4.0
was finalized, parsers also accept the deprecated aliases
`conservativeCsrTerminationProof`,
`nativeCsrTerminationProof` and
`nativeConservativeCsrTerminationProof`. They have exactly the same
semantics as their canonical counterparts.

CPF 4.0 does not currently add a context-sensitive nontermination proof.

## Right-Forward Closures

CPF 4.0 adds the following processors below `trsTerminationProof`:

- `rfcBounds`
- `rfcAutomatonClosedBounds`
- `rfcRelativeBounds`
- `rfcAutomatonClosedRelativeBounds`
- `rfcMatchboxRelativeBounds`
- `rfcNativeMatchboxRelativeBounds`

Each RFC processor records `initialTerms` followed by the ordinary
CPF bounds certificate. Relative variants additionally record the
remaining TRS and recursive termination proof.

## Compatibility

CPF 4.0 processors are optional extensions. A certifier may reject an
unsupported CPF 4.0 processor, but it must not interpret an unknown
processor as an assumption or an ordinary CPF 3.x proof step.
