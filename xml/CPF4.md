# Certification Problem Format 4.0

CPF 4 is an XML format for machine-checkable proofs. It preserves CPF 3 and
adds first-order term and string rewriting proof forms, including
context-sensitive rewriting, relative annotated dependency pairs (ADPs),
right-forward closures, cycle witnesses and conditional rewriting.
It is the extended dialect implemented by this Ferrum/CeTA repository;
the version name does not imply adoption as an external standard.

This guide is for certificate producers and users of CeTA. For the inherited
format, see the official [CPF 3 and CeTA 3 guide](https://isafor-ceta.uibk.ac.at/cpf3.html).
The [category map](CERTIFICATE_FORMATS.md) describes the wider interfaces.

## Files and prerequisites

- [cpf4.xsd](cpf4.xsd) is the entry-point schema. Keep it alongside its includes:
  [lts.xsd](lts.xsd), [cpf4-composition.xsd](cpf4-composition.xsd),
  [cpf4-native.xsd](cpf4-native.xsd) and [cpf4-ferrum.xsd](cpf4-ferrum.xsd).
- The XSD declarations and their annotations give the exact element order,
  types and multiplicities. Element names and capitalization are significant.
- Use the unified CeTA executable built from this repository. Stock CeTA 3
  is not sufficient for the added proof forms.

Commands below run from the CeTA repository root. To build, install Python 3,
GHC and the Haskell packages required by the [build instructions](../README),
then run:

```sh
make ceta
./ceta --list-categories
```

The default executable is `./ceta`. An existing private build can instead be
used by substituting its path in the commands below. `./ceta --version`
reports the checker version, not the maximum CPF format version.

## A complete certificate

This certificate proves termination of the empty TRS. It is also available as
[examples/cpf4-empty-trs.xml](../examples/cpf4-empty-trs.xml).

```xml
<?xml version="1.0" encoding="UTF-8"?>
<certificationProblem xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance"
                      xsi:noNamespaceSchemaLocation="../xml/cpf4.xsd">
  <cpfVersion>4.0</cpfVersion>
  <lookupTables/>
  <input><trsInput><trs><rules/></trs></trsInput></input>
  <property><termination/></property>
  <answer><yes/></answer>
  <proof><trsTerminationProof><rIsEmpty/></trsTerminationProof></proof>
</certificationProblem>
```

The schema path here is relative to a document in `examples/`; adjust it when
moving the document. No network access is required to validate it.

The envelope contains, in order:

1. `cpfVersion`: use `4.0` for new CPF 4 certificates.
2. `lookupTables`: inherited term/rule indexing tables, or an empty element.
3. `input`: the problem being certified, including its rewriting strategy.
4. `property`: the claim, such as `termination`.
5. `answer`: `yes` or `no` for a binary claim.
6. `proof`: the proof tree or structured witness.
7. Optional `metaInformation`, as specified by the schema.

CPF 3's optional property/answer fields remain available for inherited proof
forms. New cycle and conditional witness envelopes require explicit matching
property/answer fields and empty lookup tables. Use the complete form above
when producing a self-contained certificate.

A termination proof must discharge its residual obligations. A `no` answer
requires a nontermination witness; failure to find a termination proof is not
such a witness. Rule-removal steps inherited from CPF 3 name the **removed**
rules, not the remaining rules. Rule references must resolve in the lookup
table, and strategies, strict/weak rules and assumptions must be preserved
throughout a proof tree.

## Validate syntax and check the proof

With libxml2's `xmllint` installed:

```sh
xmllint --huge --noout --schema xml/cpf4.xsd examples/cpf4-empty-trs.xml
./ceta --category cpf examples/cpf4-empty-trs.xml
```

The second command should print `CERTIFIED` and exit with status 0.
The `cpf` category is the default, so `./ceta examples/cpf4-empty-trs.xml`
is equivalent. Schema validity checks structure; CeTA checks the proof.
Neither alone establishes correspondence to an independently supplied source
problem unless that correspondence is checked too.

For proofs deeper than libxml2's nesting limit, use the included streaming
validator with Java 11 or newer. Its input is one certificate filename per line:

```sh
printf '%s\n' examples/cpf4-empty-trs.xml |
  java -Xss64m -Xmx8g tests/unified/ValidateCpf4.java xml/cpf4.xsd
```

It prints `OK` or `ERROR` for each file and returns nonzero if any fail.

## Select the checker interface

All commands below use the same unified executable. The filename suffix does
not select the interface. These examples are schema-valid, runnable proofs:

| Proof family | Example command |
| --- | --- |
| Ordinary/relative TRS, CSR, RFC and ADP | `./ceta --category cpf examples/cpf4-empty-trs.xml` |
| Cycle nontermination | `./ceta --category cycle tests/unified/cpf4-first-order/cycle.xml` |
| Ordinary conditional nontermination | `./ceta --category conditional --ordinary tests/unified/cpf4-first-order/conditional.xml` |
| Operational conditional nontermination | `./ceta --category conditional tests/unified/cpf4-first-order/conditional-operational.xml` |
| Conditional termination by erasure | `./ceta --category conditional-erasure tests/unified/cpf4-first-order/erasure.xml` |

Ordinary conditional termination concerns actual conditional rewriting.
Operational termination also concerns condition evaluation. An infinite
operational call sequence alone does not prove ordinary nontermination.

For `cpf`, the normal results are `CERTIFIED` (exit 0), `REJECTED` (exit 1),
and `UNSUPPORTED` (exit 2). Read stderr for the reason. Other category adapters
also require `CERTIFIED` with exit 0 for success; do not assume their failure
codes distinguish unsupported syntax from an invalid proof. Missing files and
other runtime errors are not certification results.

## Bind certification to an external problem

For the `cpf` interface, supply independently obtained input, property and
answer to prevent a producer from proving a different problem:

```sh
./ceta --category cpf --inputf examples/cpf4-empty-trs.input.xml \
  --property SN --answer YES examples/cpf4-empty-trs.xml
```

The [input file](../examples/cpf4-empty-trs.input.xml) contains an `input`
element, not a whole `certificationProblem`. In a competition or batch runner,
the trusted input converter must generate this file from the original problem,
including its strategy and strict/weak rules. Extracting it from an untrusted
certificate does not provide independent source binding.

The inherited shorthand identifiers are:

| Property | CLI value |
| --- | --- |
| Termination, including relative termination | `SN` |
| Confluence | `CR` |
| Commutation | `COM` |
| Infeasibility | `INF` |
| Runtime complexity | `RC` |
| Derivational complexity | `DC` |

Binary answers are `YES` or `NO`. Polynomial upper bounds use
`WORST_CASE(?,O(n^d))`, replacing `d` with an integer degree; quote this argument
in a shell. `--propertyf` accepts an XML `property` element and `--answerf`
accepts an answer from a file. The corresponding string options are
`--property` and `--answer`.

These options belong to the `cpf` interface. For cycle and conditional
interfaces, independently compare the embedded input with the original source:
ordered rules and conditions, strategy, property and answer must match.
Do not pass ordinary TRS options to those interfaces or treat a proof of a
translated TRS alone as a proof of the original conditional problem.
Do not use `--allow-assumptions` for a closed, independently certified result.

## Added first-order proof forms

### Context-sensitive rewriting

The replacement map is stored under
`input/trsInput/strategy/contextSensitive`. The source signature is part of
the obligation: CSR termination concerns terms over that signature.

`csrTerminationProof` supports CSR rule removal and dependency pairs.
`csrImprovedDependencyPairs` implements the exact LPAR'08 construction with
an explicit fresh unhiding symbol and recomputed ordinary, collapsing,
hidden-term and hiding-projection pairs. Its `csrDpProof` supports empty
problems, ordinary DP suffixes, dependency graphs, usable rules, subterm
criteria, instantiation and size-change proofs.

Conservative certificates use `conservativeCsrTerminationProof` with auxiliary
weak rules. The older `nativeCsrTerminationProof` and
`nativeConservativeCsrTerminationProof` spellings remain accepted aliases.
An ordinary DP continuation is wrapped as
`csrDpProof/ordinaryDpProof/dpProof`.

Typed MU-TERM and guarded/source proof wrappers are declared in
[cpf4-ferrum.xsd](cpf4-ferrum.xsd). `expandedExtendedBasicCsrProof` and
`expandedStrongUsableRulesProc` refer to expanded pairs. Their pair references
must use the expanded variable names from `string_renameN`, for example
`x0_x`, rather than the original `x`. An unmatched reference removes no pair.
CPF 4 does not add a dedicated CSR nontermination constructor.

Examples: [CSR unhiding](../examples/csr_innermost_unhiding_projection.cpf.xml),
[conservative CSR](../tests/unified/cpf4-csr-aliases/conservative.xml), and
[typed CSR proofs](../tests/unified/cpf4-typed-extensions).

### Right-forward closures

Below `trsTerminationProof`, CPF 4 adds `rfcBounds`,
`rfcAutomatonClosedBounds`, `rfcRelativeBounds`,
`rfcAutomatonClosedRelativeBounds`, `rfcMatchboxRelativeBounds` and
`rfcNativeMatchboxRelativeBounds`. They record `initialTerms` followed by
bounds evidence; relative variants also record residual rules and the
recursive termination proof. Consult the declarations in
[cpf4.xsd](cpf4.xsd) for each variant's fields.

Example: [RFC bounds](../tests/unified/cpf4-rfc-variants/positive.xml).

### Relative annotated dependency pairs

`relativeAdpComposition` combines an ordinary recursive proof with explicit
relative-ADP discharges. Each discharge identifies the exact strict and weak
rules. Every termination assumption in the ordinary proof must be covered
and each ADP discharge must itself check successfully.

This supports ADP children following ordinary transformations such as
uncurrying or DP-to-TRS switching. ADP-to-ordinary-to-ADP crossing inside
derelatification is not supported. See
[cpf4-composition.xsd](cpf4-composition.xsd) and the
[relative ADP example](../examples/relative_adp_rt1_3.cpf.xml).

### Cycle and conditional witnesses

| Family | Input | Property / answer | Proof constructor |
| --- | --- | --- | --- |
| Cycle nontermination | `cycleInput` | `termination` / `no` | `CycleEmbedding`, `CycleTransport`, `CycleMorphism` |
| Conditional nontermination | `conditionalInput` | `termination` or `operationalTermination` / `no` | `ConditionalCycle`, `ConditionalLoop` |
| Conditional erasure | Original conditional TRS input | `termination` / `yes` | `conditionalErasureProof` containing `trsTerminationProof` |

The witnesses are structured XML, not embedded textual Haskell values.
[cpf4-native.xsd](cpf4-native.xsd) specifies their field grammar. The runnable
examples in the interface table show complete documents. Erasure certificates
use the CPF envelope, not a standalone `conditionalErasureProof` document.

### Other first-order additions

[cpf4-ferrum.xsd](cpf4-ferrum.xsd) also describes sparse tiling/removal,
GM04 transformations, outermost Raffelsieper–Zantema transformations,
innermost Q-DP and AAECC proofs, and CSR source/typed/guarded wrappers.
Each constructor has its own semantic side conditions; choosing a matching
XML tag is not sufficient to establish its conclusion.

## Compatibility and migration

CPF 4 preserves CPF 3 vocabulary and semantics, including its original LTS
constructs. Existing CPF 3 documents need no conversion for this checker.
For new documents using only inherited forms, change `cpfVersion` to `4.0`
and point the schema location at `cpf4.xsd`; then validate and certify again.
New CPF 4 forms cannot be made CPF 3 compatible merely by changing the version.

For CPF 2 input, first use the upstream converter described in the
[CPF 3 guide](https://isafor-ceta.uibk.ac.at/cpf3.html), then follow the steps
above. This checkout does not provide a general converter for old textual
cycle/conditional witnesses or standalone erasure documents. Legacy readers
remain available for historical certificates; generate new proofs with
Ferrum's CPF 4 output instead.

CPF 5 adds ITS and higher-order extensions; CPF 6 additionally adds LP, LP
with cut and Prolog extensions. These additions are outside CPF 4. In
particular, the later ITS `div`/`mod` and nontermination extensions do not
belong to CPF 4. [cpf4-legacy-its.xsd](cpf4-legacy-its.xsd) preserves an earlier
experimental dialect; it is not the schema to use for new CPF 4 files.

## Viewing certificates and diagnosing failures

The inherited [CPF 3 stylesheet](../examples/cpf3HTML.xsl) can help display
inherited proof forms, but there is no complete CPF 4 HTML renderer in this
checkout. It must not be relied on to display all extension steps. Use an XML
viewer or formatted XML for those certificates; rendering never certifies a
proof.

- **Schema error:** check element order, spelling, namespace and included XSD
  files. A `csrDpProof` wrapper cannot be replaced by a bare `dpProof`.
- **Unsupported proof:** check the selected category and whether the executable
  includes the extension. A format version alone does not imply support.
- **Rejected proof:** read the checker diagnostic; check residual rules,
  pair references, replacement maps and discharge obligations.
- **Source mismatch:** verify the original input and property independently;
  a valid certificate for another problem does not establish the requested claim.
- **Depth error:** try the streaming schema validator above.

For maintainers, validation evidence and development history are kept in the
[integration record](../docs/state-local-integration.md) and the
[CPF 4 validation report](../docs/data/cpf4-milestone-20261126/final-summary.json).
