# CeTA: certified termination analysis

CeTA checks termination and nontermination certificates using executable code
obtained from Isabelle/HOL soundness proofs. This repository extends CeTA/IsaFoR
with first-order rewriting processors and **CPF 4**, extending CPF 3 with
additional proof constructors and recursive certificate composition.

The supported first-order categories are standard, innermost, outermost,
relative, context-sensitive, equational, ordinary conditional, and operational
conditional term rewriting, and standard, relative, and cycle string rewriting.
Cycle certificates establish nontermination. All first-order certificates use
CPF 4 XML, including cycle witnesses, conditional nontermination, and conditional
erasure. The unified executable selects the checker for each certificate form.

## Build the unified checker

Requirements: Python 3, GNU Make, GHC and `ghc-pkg` (with `base` and `array`), and
`ar` on `PATH`.

```sh
make ceta
./ceta --list-categories
```

The build compiles committed, hash-verified Haskell exports from Isabelle and
links their checking interfaces into **one executable**, `./ceta`. It does not
require Isabelle to be installed. Build products and identities are stored under
`target/unified/`; `target/unified/build.json` records the resulting binary hash.

To adjust parallelism or select GHC:

```sh
make ceta CETA_BUILD_JOBS=2 GHC=/path/to/ghc
```

Keep the matching `ghc-pkg` on `PATH` (or set `GHC_PKG`). `CETA_BIN_DIR` changes
the destination of the executable. Use `make test` to exercise the bundled
examples; inspect its per-example results.

## Check first-order proofs

For ordinary CPF certificates, including dependency-pair, relative, equational,
context-sensitive, and unravelling proofs:

```sh
./ceta proof.cpf.xml
```

Successful checking prints `CERTIFIED`; rejection exits unsuccessfully. The
certificate specifies its input, property, answer, and proof. The following
forms use explicit entry points in the same executable:

```sh
# Cycle nontermination
./ceta --category cycle cycle.cpf.xml

# Operational conditional nontermination
./ceta --category conditional operational-no.cpf.xml

# Ordinary conditional nontermination
./ceta --category conditional --ordinary ordinary-no.cpf.xml

# Ordinary conditional termination by condition erasure
./ceta --category conditional-erasure erasure.cpf.xml
```

These are **CPF 4 XML certificates**, not separate proof formats. Conditional
termination by unravelling uses the ordinary `./ceta proof.cpf.xml` entry point.
The category switches select checking code; they do not change the certified
rewrite semantics.

The schema is [xml/cpf4.xsd](xml/cpf4.xsd), with the constructors documented in
[CPF4.md](xml/CPF4.md). XML schema validation checks syntax; CeTA checks the proof.
For a complete certificate, every residual obligation must be discharged; do
not enable assumption acceptance when checking a claimed complete proof.

## Generate certificates with Ferrum

[Ferrum](https://github.com/schneiderkamplab/ferrum) searches for proofs and emits
CPF 4. Its category-specific adapters also bind the certificate to the original
ARI input and requested answer before invoking this checker:

```sh
../ferrum/target/release/ferrum prove input.ari \
  --no-top-level-llm --cpf-mode cpf40 --cpf proof.cpf.xml
../ferrum/target/release/ferrum cert check-standard \
  input.ari proof.cpf.xml --answer yes --ceta ./ceta
```

Use `--answer no` for nontermination and the matching adapter for other
categories. Ferrum's [README](https://github.com/schneiderkamplab/ferrum/blob/main/README.md)
contains a complete example, a category command table, and a lock-step script
that generates and checks each proof before accepting the result.

## Formalization and repository layout

- `thys/`: Isabelle theories, processor soundness proofs, and code exports.
  `thys/Category_Specifications/` defines the category semantics.
- `scripts/unified-exports.json`: checked export archives, source hashes, and
  unified-checker adapters.
- `src/Haskell/`: input parsing and executable interfaces.
- `xml/`: CPF schemas and format documentation.
- `examples/` and `tests/unified/`: certificates and integration checks.
- `COPYING` and `COPYING.LESSER`: licence texts.

Rebuilding formalizations and regenerating exports requires Isabelle2025-2 and
the matching Archive of Formal Proofs dependencies. See the session-specific
instructions in `thys/` and the Isabelle targets in the Makefile. Generated
checking logic is obtained by code export, not edited by hand.

The unified executable also includes program-analysis interfaces. See the
[format map](xml/CERTIFICATE_FORMATS.md) and [integration documentation](docs/state-local-integration.md)
for their semantics and entry points. The [upstream CeTA/IsaFoR site](https://isafor-ceta.uibk.ac.at/)
describes the original certifier and formal library.
