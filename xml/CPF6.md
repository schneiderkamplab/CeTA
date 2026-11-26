# CPF 6: logic programming, cut and Prolog

CPF 6 is CPF 5 plus logic-programming additions. It inherits every CPF 3, CPF 4
and CPF 5 form: CPF 4 adds first-order term and string rewriting, CPF 5 adds ITS
and higher-order rewriting, and CPF 6 adds LP, LP with cut and Prolog. An XML
schema describes certificate syntax; only successful mathematical checking
establishes the claimed result.

## Build and check

Build the unified executable from the committed, hash-verified Isabelle exports:

```sh
make ceta
./ceta --category lp proof.cpf.xml
./ceta --category prolog prolog-proof.cpf.xml
```

Two small, checked examples are [finite-term LP](../examples/cpf6-finite-lp.xml)
and [an undefined Prolog query](../examples/cpf6-undefined-prolog.xml):

```sh
./ceta --category lp examples/cpf6-finite-lp.xml
./ceta --category prolog examples/cpf6-undefined-prolog.xml
```

Both LP and LP-with-cut use `--category lp`. Prolog uses `--category prolog`;
an LP residual alone is not a Prolog source proof. A successful check exits zero
and prints a category-specific `CERTIFIED ...` verdict. A missing, malformed or
semantically invalid proof fails. `--diagnostics` is deliberately non-accepting.
The checker accepts historical standalone XML fragments for compatibility;
new Ferrum exports always use the CPF 6 document envelope. Unsupported exports
fail explicitly instead of falling back to standalone fragments.

Generate and source-bind certificates using Ferrum's `prove-lp`, `prove-lp-cut`
and `prolog-prove` commands. Pass `--ceta /absolute/path/to/ceta`. Source audit
and two successful checker invocations are required before accepting a source
verdict. `logic-programming-audit` and `logic-programming-cut-audit` check original
LP/cut input correspondence; Prolog's production path binds its complete source
before certification. A proof can be mathematically valid for the input embedded
in the certificate while still not describe the source file you intended.

## Envelope and semantics

A CPF 6 LP/Prolog document has the ordered children `cpfVersion` (`6.0`),
`lookupTables`, `input`, `property`, `answer`, and `proof`. The property is
`termination`; `yes` proves termination under the specified query assumptions,
while `no` proves nontermination. There must be exactly one input, answer and
proof. Duplicate or reordered fields, extra evidence, wrong versions and
mismatched claim polarity are rejected by the adapter.

| Input | Meaning |
| --- | --- |
| `logicProgramInput` | Ordered program and query, with `finiteTerms` or `infiniteTrees` resolution semantics. |
| `logicProgramWithCutInput` | Ordered cut program and query modes, with the constructor's checked cut semantics. |
| `logicProgramTriplesInput` | Complete dependency-triple residual and support program, with their query and semantics. |
| `prologInput` | `executionProfile`, complete ordered `program`, and `query` containing `predicate` and `modes`. |

The Prolog execution profile is `iso-rational-libraries-v1`. It identifies the
existing checked operational semantics; it does not assert support for every
implementation-dependent Prolog feature. Clause order, arities, query modes,
cut scopes, saved alternatives, builtin behavior, numeric domains and source
preprocessing are part of the proof's subject. Each proof constructor retains
its own side conditions. Do not interchange rational-tree, finite-term, ground
integer or machine-number evidence simply because the outer profile matches.

Source fields occur in `input`. Proof fields contain witnesses and residual
proofs. The adapter reconstructs exactly the existing Isabelle parser's input;
it never replaces a proof obligation with a producer verdict. Recursive LP
children use their own CPF envelopes where specified by the constructor. Inline
TRS, DP and numeric children use the inherited CPF proof grammar. Previously
recorded ITS child documents can retain their historical version; this is
backward-compatible reading, not a new ITS addition to CPF 4.

## Schema files

Validate complete documents against `cpf6.xsd`, for example with an XML Schema
1.0 validator. Its included files are:

- `cpf6-logic-programming.xsd`: LP and triple residual forms.
- `cpf6-cut.xsd`: ordered-cut graph, SEG, return and nontermination forms.
- `cpf6-prolog.xsd`: static, contextual, established, finite and guarded Prolog forms.
- `cpf6-prolog-source.xsd`: remaining mixed, numeric and operational Prolog forms.
- The inherited CPF 3–5 schemas and extension grammars.

`cpf6-prolog-source-forms.json` records field order and source parser locations
for the added source forms. `scripts/generate_cpf6_source_schema.py` extracts
structured syntax from the existing Isabelle parser combinators and fails on
unknown combinators. It emits no wildcard evidence types. Syntactic validation
does not check arithmetic, graph closure, ranking, source equality or recursive
child proofs; CeTA does.

## Proof families

The [coverage inventory](cpf6-coverage.json) lists all 71 source/residual forms
in the current CPF 6 grammar and their source parsers. Residual forms may be
checked as children of a source proof rather than as standalone source claims.
The experimental context-reference formalization is not a dispatched/exported
checker interface and is excluded explicitly.

Ordinary LP includes finite-term and TOCL09 translation, source loops, traces,
unification and neutral loops, recurrent pairs, affine and pattern loops,
PiDP/mode/simplification, source and answer graphs, constructor QDP, and initial
dependency triples. Cut forms include source loops and uniform recursion,
operational/constructor/MGU graphs, SEG variants, and return, module, composed,
nested and projected reductions. Their complete field definitions and recursive
child contracts are in the [constructor reference](CPF6-development-history.md).
Historical validation statements in that reference describe their recorded
checkpoints, rather than the current milestone status.

Prolog source forms include static bridges, undefined queries, variable and
modular returns, contextual and composed triples, established finite/nonfinite
triple reductions, finite direct evaluation, guarded/mixed reductions, numeric
call/recurrence reductions, and source nontermination traces. Full program
and query binding is mandatory even for undefined queries: the generated
checker uses definition signatures, but the adapter first validates them against
the complete source. Legacy undefined-query proofs need the original source
when converted; signatures alone cannot reconstruct that source.

Stopped mixed proofs may use an empty `enclosingTransferContract` reference.
The generated parser resolves it to the unique enclosing transfer contract
before mathematical checking. It is not an unchecked assumption or a reference
to a previously accepted result. Optional success-case and normalization fields
retain their parser defaults; they are not dropped during transport.

The additional source forms have the following ordered evidence fields. `?`
marks an optional field; `|` marks alternatives. Source/profile/query fields are
in the outer input and are not repeated below.

| Constructor | Answer | Evidence fields |
| --- | --- | --- |
| `prologBinary64SourceNonterminationProof` | no | `fuel`, `arguments`, `core / coreGoals`, `before`, `after`, `prefix`, `loop` |
| `prologContextITSProof` | yes | `fuel`, `roots`, `regions`, `prologNumericComponent` |
| `prologDomainGraphNonterminationProof` | no | `version`, `fuel`, `arguments`, `prefix`, `corePredicate`, `coreArguments`, `pending`, `saved`, `observations`, `initialRecipes`, `entry`, `modules` |
| `prologEstablishedFiniteSEGGuardedProof` | yes | `fuel`, `chainPredicate`, `triples`, `successProgram`, `prologSuccessTransferContract`, `contexts`, `roots`, `components`, `observedTriples`, `guardedDescents`, `argumentProjection`, `prologNumericComponent` |
| `prologEstablishedFiniteLocalSEGMixedProof` | yes | `signatures`, `fuel`, `chainPredicate`, `triples`, `successProgram`, `prologSuccessTransferContract`, `contexts`, `roots`, `components`, `observedTriples`, `guardedDescents`, `routing`, `backends` |
| `prologGuardedDomainGraphNonterminationProof` | no | `version`, `fuel`, `arguments`, `prefix`, `corePredicate`, `coreArguments`, `pending`, `saved`, `observations`, `initialRecipes`, `entry`, `modules` |
| `prologHelperIntegerCallsProof` | no | `observations`, `interfaces`, `callEdges`, `numericChild` |
| `prologIntegerCallsProof` | no | `interfaces`, `callEdges`, `numericChild` |
| `prologIntegerRecurrenceProof` | no | `clause`, `variables`, `operations`, `outputs`, `coordinates`, `location`, `numericChild` |
| `prologCallTraceNonterminationProof` | no | `version`, `fuel`, `arguments`, `prefix`, `core`, `pending`, `saved`, `reserved`, `interface`, `calls`, `traces` |
| `prologPartialIntegerCallsProof` | no | `observations`, `interfaces`, `callEdges`, `numericChild` |
| `prologScalarDomainRecurrenceNonterminationProof` | no | `version`, `fuel`, `arguments`, `prefix`, `corePredicate`, `coreArguments`, `pending`, `saved`, `observations`, `initialRecipes`, `selection`, `variables`, `actions`, `outputs`, `recipes`, `failures` |
| `prologScalarRecurrenceNonterminationProof` | no | `observations`, `selection`, `variables`, `actions`, `outputs`, `recipes`, `failures` |
| `prologEstablishedStableSEGMixedProof` | yes | `fuel`, `chainPredicate`, `triples`, `successProgram`, `prologSuccessTransferContract`, `contexts`, `roots`, `components`, `observedTriples`, `routing`, `backends` |
| `prologEstablishedStoppedSEGMixedProof` | yes | `fuel`, `chainPredicate`, `triples`, `successProgram`, `prologSuccessTransferContract`, `contexts`, `roots`, `components`, `observedTriples`, `successCases?`, `equationNormalizationFuel?`, `normalizedTriples?`, `routing`, `backends` |


## Limits and troubleshooting

Use the correct category switch and requested answer. Check the version,
execution profile, source program/query and the exact residual kind before
investigating a failed mathematical check. Incomplete graph evidence, false
child proofs, unsupported builtin operations, incorrect modes and missing
arithmetic side conditions must be rejected. An unknown search result has no
certificate to validate; it is distinct from a rejected certificate.

LeTA implementation and validation are deferred. Historical dual-checker
checkpoints do not establish current LeTA coverage. Current CeTA validation
records are maintained separately from this end-user format reference.
