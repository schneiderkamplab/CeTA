# Certificate formats across the production categories

For first-order certificate users, start with the [CPF 4 user guide](CPF4.md):
it includes runnable examples, validation and checking commands, and source
binding instructions.

This is the entry point for the certificate interfaces across rewriting, ITS,
and logic programming, including cut and Prolog. It documents candidate
interfaces and their remaining migration gaps. Production deployment still
depends on the pinned checker binary.

The versions are additive: [CPF 4](CPF4.md) preserves all of CPF 3 and adds
first-order term and string rewriting; [CPF 5](CPF5.md) adds ITS and
higher-order rewriting extensions; [CPF 6](CPF6.md) adds LP, LP with cut,
and Prolog extensions. Existing CPF 3 LTS constructs remain inherited.
Schema support, independent checker coverage, and fresh replay are separate
acceptance requirements; the full migration has not yet passed all three.

## Format and semantics map

| Category | Certificate interface and reference | Required source context |
| --- | --- | --- |
| TRS Standard | [CPF4](CPF4.md) (explicit legacy CPF modes retained) | Original rules, full rewriting |
| TRS Innermost | CPF with innermost strategy and strategy-switch proofs | Original rules and innermost strategy; Q contexts in intermediate DP states |
| TRS Contextsensitive | [CPF4 CSR extensions](CPF4.md#context-sensitive-rewriting) | Original rules, replacement map and signature |
| SRS Standard | String systems represented through the first-order CPF interfaces, including bounds/RFC | Original string rules and their first-order representation |
| TRS Relative | Relative CPF and [relative ADP integration](../thys/Relative_ADP/README.md) | Strict and weak rules, kept distinct |
| SRS Relative | Relative CPF, including [relative RFC extensions](CPF4.md#right-forward-closures) | Strict and weak string rules and their representation |
| TRS Outermost | CPF strategy/checked transformation interfaces | Original rules and outermost strategy, not unrestricted termination of an unrelated residual |
| TRS Equational | CPF interfaces and the supported equational checker path | Rewrite rules and equations, with the intended rewriting-modulo relation |
| SRS Cycle | [Structured CPF4 cycle witnesses](CPF4.md#first-order-envelope-and-structured-witnesses) | Original string rules; rewriting modulo rotation requires genuine rewrite progress |
| TRS Conditional (operational) | CPF4 termination and structured operational descent/loop certificates | Original ordered conditions; operational calls and condition evaluation matter |
| TRS Conditional (ordinary termination) | CPF4 source-bound erasure and structured conditional loops in `--ordinary` mode | Original conditional rules; nontermination must establish actual conditional rewriting, not just divergent condition evaluation |
| Higher-order rewriting | [CPF5 structured proofs and embedded delegation](CPF5.md); explicit `--legacy` native compatibility | Original typed signature and rules, binding/substitution and the declared higher-order relation |
| Logic programming | [CPF6 translation, Pi-DP composition and source nontermination forms](CPF6.md); remaining constructors still use separate XML during migration | Original clauses, query pattern and resolution semantics; a translated TRS certificate alone is insufficient |
| Logic programming with cut | [CPF6 graph, source-NO, SEG, SEG-triple and nested/composed-return forms](CPF6.md); remaining return forms still use separate XML during migration | Original ordered clauses, cut control and query pattern; recursive Split and successful-prefix obligations |

ITS additions use the CPF5 schema (`lts5.xsd`) and the version-gated `its`
interface. Historical CPF3/4 ITS extensions require `--legacy`; original CPF3
LTS proofs remain supported by `cpf`. Independent LeTA integration is deferred. LP with cut and Prolog additions
are assigned to CPF6. Ten cut forms have focused integration gates; the remaining standalone
XML producers/checker paths still require migration. Prolog additionally retains its ordered operational
semantics, builtin behavior and source query context; an LP proof is not a
substitute for those obligations.

This map identifies interface families, not a claim that every processor in
every family is supported by every binary. Production manifests pin the actual
checker executable and its hash. Follow the executable parser and its generated
checker for the exact accepted grammar and side conditions.

## CPF and remaining native interfaces

[cpf4.xsd](cpf4.xsd) covers the first-order CPF dialect described in
[CPF4.md](CPF4.md), including the structured cycle and conditional forms.
These are extensions of CPF, not separate textual or standalone XML formats.
The cycle/conditional legacy readers remain available for existing artifacts.

Higher-order CPF5 proofs embed structured source/witness data and any
first-order child. The eighteen integrated pure-LP CPF6 forms and ten cut forms separate
source program/query from proof evidence. Other LP/cut/Prolog forms still use
separate XML. Automatic legacy readers remain a staging measure pending explicit legacy
interfaces. A version label alone does not migrate a certificate. These version
names do not assert adoption by an external standards body.

## LP and cut-aware SEG/triples layers

The independently exposed [dependency-triples XML layer](../thys/Logic_Programming/LP_Dependency_Triple_XML.thy)
and [export](../thys/Logic_Programming/LP_Dependency_Triple_Code.thy) must not be
confused with source-program certification. They check an intermediate problem.
The [cut-aware source endpoint](../thys/Logic_Programming/LP_Cut_SEG_Triple_XML.thy)
connects the original program/query to the graph, recursive Split receipts,
dependency triples and Pi-DP obligations. Its theorem
`check_lpc_seg_triples_xml_sound` supplies the source-level conclusion.

The integrated cut checker also retains return-module, projected, SEG and
nontermination endpoints; its build flags determine which generated interfaces
are linked. See [build_lp_seg_driver.sh](../scripts/build_lp_seg_driver.sh).
The [finite-term LP driver](../src/Haskell/Main_LP_Finite.hs) explicitly has a
narrower semantic claim and must not silently replace the TOCL09 interface.

## Acceptance and compatibility

1. Preserve the original input and its category-specific context in the
   certificate and independently audit their correspondence with the benchmark.
2. Check each transformation and its residual obligations. An open fragment or
   intermediate problem certificate is not a source termination proof.
3. Reject unsupported tags, malformed data and missing obligations. Never
   reinterpret them as assumptions or as a weaker category.
4. XML/schema validation establishes syntax only. Acceptance requires the
   applicable verified executable checker and its semantic side conditions.
5. Retain checker hashes, proof artifacts, original-input audits and repeated
   certification in the production acceptance record. Oracle guidance is search
   advice and is not a certificate or an additional trusted premise.

The historical fourteen-category production catalog and current replay ledger live in the sibling
Ferrum repository: `oracles/production/20261025-v145/catalog.json` and
`docs/state-of-the-art.md`. They record tested root sets, not format standards.
