# Certification Problem Format 5.0

CPF 5 preserves CPF 4, including every CPF 3 construct, and adds integer
transition-system (ITS) and higher-order rewriting certificates. CPF 4 adds
first-order term and string rewriting. Logic programming, LP with cut and
Prolog additions belong to [CPF 6](CPF6.md). Existing CPF 3 LTS features remain
inherited: moving later ITS extensions to CPF 5 removes no CPF 3 feature.
These version names describe this Ferrum/CeTA dialect, not an external standard.

This guide complements the [CPF 4 user guide](CPF4.md) and the official
[CPF 3 guide](https://isafor-ceta.uibk.ac.at/cpf3.html).

## Files and checking

Use [cpf5.xsd](cpf5.xsd) with its sibling includes: [lts5.xsd](lts5.xsd),
[cpf5-higher-order.xsd](cpf5-higher-order.xsd),
[cpf4-composition.xsd](cpf4-composition.xsd),
[cpf4-native.xsd](cpf4-native.xsd) and [cpf4-ferrum.xsd](cpf4-ferrum.xsd).
The XSDs specify exact field order, types and multiplicities. Keep the files
together when installing the schema. The format is structured XML; native
text witnesses are not CPF 5 documents.

Build the unified checker with `make ceta` as described in the [README](../README).
Commands here run from the CeTA repository root; substitute a private checker
path for `./ceta` if needed. Schema checking and mathematical checking are
separate operations:

```sh
xmllint --noout --schema xml/cpf5.xsd examples/cpf5-empty-higher-order.xml
./ceta --category higher-order examples/cpf5-empty-higher-order.xml
```

A successful checker exits zero and prints `CERTIFIED`. A schema-valid document
can still contain an invalid proof. Conversely, a checker invocation alone
does not establish that the encoded input matches an external source file.
Use Ferrum's source audit as well when validating exported proofs against the
original problem.

## Envelope and example

New documents use `cpfVersion` 5.0 and the usual `certificationProblem` envelope.
The input, property, answer and proof must agree. This complete example proves
termination of the empty higher-order system and is saved as
[cpf5-empty-higher-order.xml](../examples/cpf5-empty-higher-order.xml):

```xml
<?xml version="1.0" encoding="UTF-8"?>
<certificationProblem>
  <cpfVersion>5.0</cpfVersion>
  <lookupTables/>
  <input><higherOrderInput><signature/><rules/></higherOrderInput></input>
  <property><termination/></property>
  <answer><yes/></answer>
  <proof><ho-termination><certificate><empty/></certificate></ho-termination></proof>
</certificationProblem>
```

The higher-order interface uses explicit source declarations and rules and an
empty lookup table. Use the field names and nesting in its schema; constructor
names are case-sensitive. Use `termination` for the property and `yes` or `no`
according to the proof's polarity. A wrong version, property or polarity is
rejected even if the nested proof data would otherwise be valid.

## Integer transition systems

ITS input is an `lts` graph. The ITS interface uses
`<lookupTables><ruleTable/></lookupTables>` and explicit graph identifiers. Termination uses `ltsTerminationProof`;
nontermination uses `ltsNonterminationProof`. Invoke:

```sh
./ceta --category its certificate.xml
```

A complete [acyclic ITS example](../examples/cpf5-acyclic-its.xml) can be checked with:

```sh
xmllint --noout --schema xml/cpf5.xsd examples/cpf5-acyclic-its.xml
./ceta --category its examples/cpf5-acyclic-its.xml
```

The termination interface retains cooperation proofs, ranking functions,
invariants and the inherited graph transformations. CPF 5 extends expressions
with binary `div` and `mod`. For any integer numerator n and nonzero signed
divisor d, their values q and r satisfy n = d*q + r and 0 <= r < |d|.
For example, div(-5,-2) = 3 and mod(-5,-2) = 1. Expressions may be nested.
CeTA accepts only closed, nonzero divisor expressions; symbolic and zero
divisors are rejected. The schema admits more expressions than this checked
arithmetic fragment. In particular, schema validity is not permission to use
zero divisors, and this interface assigns them no accepted proof semantics.

Nontermination has three forms:

| Form | Required evidence |
| --- | --- |
| `equivalentState` | An initial state, a reachable stem and a nonempty loop returning to the same complete state. |
| `recurrentSet` | A reached region and successor policies proving that a transition remains in it. |
| `recurrentCycle` | A reached region and a nonempty sequence of policy steps preserving it around the cycle. |

Each transition and required assertion is checked. A satisfiable guard or an
abstract graph cycle by itself is insufficient. State valuations use integer
constants; omitted integer coordinates denote zero and omitted Boolean
coordinates denote false. Ferrum emits coordinates explicitly.

The parser, arithmetic normalization and mathematical checker are exported
from Isabelle. No SMT solver result is trusted as a certificate.

## Higher-order rewriting

The supported relation is simply typed curried rewriting together with beta
reduction, including steps under applications and abstractions. Bound variables
use De Bruijn indices and rule meta-variables use arity-aware substitution.
The claim concerns arbitrary well-typed terms, including open terms and terms
of functional type. It is not a claim about arbitrary matching modulo beta/eta.
The [semantic reference](../docs/higher-order-trust-boundary.md) links the
specification, declared-sort correspondence and concrete soundness theorems.

The [higher-order schema](cpf5-higher-order.xsd) defines typed terms,
signatures, rules and structured certificates. It is generated from the same
field grammar used by the XML adapter, rather than embedding a textual payload.
Use `higher-order` for direct proofs:

```sh
./ceta --category higher-order certificate.xml
```

Direct certificates include termination proofs and checked nontermination
witnesses, with nested constructor-specific arguments. The executable checks
the typed terms and the mathematical premises using the Isabelle-generated
higher-order checker. The complete constructor inventory is given by the
schema's proof root declarations, with regression examples in
[the higher-order corpus](../tests/unified/cpf5-higher-order-regressions/manifest.json).

The three `ho-ceta-` delegation forms embed their ordinary first-order child
under `firstOrderProof/trsTerminationProof`. They require no separate child
file. Invoke:

```sh
./ceta --category higher-order-delegation certificate.xml
```

Both the reduction to the first-order obligation and its child proof must
check. Empty, absent or mismatched child proofs are rejected.

## Compatibility and migration

Existing CPF 3 and CPF 4 proof forms remain inherited. For first-order
certificates, use the category and source-binding commands in the CPF 4 guide.
The original CPF 3 LTS interface remains available through `--category cpf`.
New ITS and higher-order extensions require CPF 5; CPF 6 inherits them.

Historical interfaces are explicit compatibility paths:

```sh
./ceta --category its --legacy old-its.xml
./ceta --category higher-order --legacy old-native-witness
./ceta --category higher-order-delegation --legacy old-native-witness old-child.xml
```

These commands do not turn the old file into CPF 5. To migrate, re-export with
Ferrum's CPF 5 producer, preserve the source and claim, validate the new XML,
audit it against the original input, then run the checker. Changing only the
version of a native text file or wrapping text in an XML element is insufficient.

The inherited CPF stylesheet does not provide a complete rendering for the
new ITS and higher-order forms; use the XML and schema as the reference.
For errors, first check the schema, version, category, claim and input binding,
then inspect the checker's diagnostic. Neither timeout nor unsupported input
establishes termination or nontermination.
