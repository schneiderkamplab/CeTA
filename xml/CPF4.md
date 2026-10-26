# Certification Problem Format 4.0

For all production categories, including cycle rewriting, higher-order
rewriting and LP with cut, see [Certificate formats](CERTIFICATE_FORMATS.md).
This page describes the repository's CPF4 dialect, not the separate native
certificate interfaces or an externally standardized release.

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

## Integer-transition Euclidean division and remainder

CPF4's LTS arithmetic expression grammar includes binary `<div>` and `<mod>`.
Each contains exactly two expressions: dividend, then divisor. Expressions may
be nested in guards, updates, and ranking expressions. For example:

```xml
<div><variableId>x</variableId><constant>2</constant></div>
<mod><constant>-5</constant><constant>-2</constant></mod>
```

For nonzero divisor `d`, the quotient `q` and remainder `r` are the unique
integers satisfying `n = d*q + r` and `0 <= r < abs(d)`. This is the
[SMT-LIB Ints Euclidean convention](https://smt-lib.org/theories-Ints.shtml),
not truncation toward zero or floor division for negative divisors. Examples:
`div(-5,2)=-3`, `div(-5,-2)=3`, and both remainders equal 1.

At divisor zero these operators are underspecified, as in SMT-LIB Ints.
No producer/checker may silently replace them by zero or select convenient
values to establish termination/nontermination. A checker must either preserve
the specified interpretation discipline or reject such applications; a first
verified implementation may require proof of a nonzero divisor.

`cpf4.xsd` includes `lts4.xsd`; CPF3 continues to include the unchanged `lts.xsd`.
The only grammar difference between those LTS files is these two expression
constructors. `tests/test_cpf4_lts_div_mod.py` checks this boundary and the new
constructor arities.

**Implementation status:** this adds CPF4 schema vocabulary and semantics. The
existing Isabelle IA signature, LTS XML parser, and frozen production checker do
not yet accept these constructors. Schema validation is not certification. The
schema-positive fixture `examples/its-div-mod.cpf4.xml` is not claimed as a
CeTA-certified proof. A verified arithmetic/translation extension, regenerated
checker and semantic mutation tests are required before promotion.
