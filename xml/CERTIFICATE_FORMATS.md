# Certificate formats across the production categories

This is the entry point for the certificate interfaces used by the fourteen
production categories, through logic programming with cut. It documents the
current candidate interfaces. First-order outputs have migrated to CPF 4 XML;
higher-order and logic-programming migration is deferred. Production deployment
still depends on the pinned checker binary.

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
| Higher-order rewriting | Native typed certificates and [CeTA delegation XML](../thys/Higher_Order_CeTA_Code/Higher_Order_CeTA_Code.thy); [source-bound call expansion](../thys/Higher_Order_Call_Expansion/README.md) | Original typed signature and rules, binding/substitution and the declared higher-order relation |
| Logic programming | [TOCL09 source-bound XML entry point](../src/Haskell/Main_LP_TOCL09.hs), [Pi-DP XML](../thys/Logic_Programming/LP_PiDP_XML.thy), source nontermination interfaces | Original clauses, query pattern and resolution semantics; a translated TRS certificate alone is insufficient |
| Logic programming with cut | [Integrated XML dispatcher](../scripts/LP_Cut_Integrated_Main.hs), including [SEG/triples XML](../thys/Logic_Programming/LP_Cut_SEG_Triple_XML.thy) and [NO XML](../thys/Logic_Programming/LP_Cut_NO_XML.thy) | Original ordered clauses, cut control and query pattern; recursive Split and successful-prefix obligations |

This map identifies interface families, not a claim that every processor in
every family is supported by every binary. Production manifests pin the actual
checker executable and its hash. Follow the executable parser and its generated
checker for the exact accepted grammar and side conditions.

## CPF and deferred native interfaces

[cpf4.xsd](cpf4.xsd) covers the first-order CPF dialect described in
[CPF4.md](CPF4.md), including the structured cycle and conditional forms.
These are extensions of CPF, not separate textual or standalone XML formats.
The cycle/conditional legacy readers remain available for existing artifacts.

Higher-order and LP interfaces still use their existing native or separate
XML formats. Their migration is deferred; a version label alone would not
make them CPF. The repository's CPF4 name does not assert adoption by an
external standards body.

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

The fourteen-category production catalog and replay ledger live in the sibling
Ferrum repository: `oracles/production/20261025-v145/catalog.json` and
`docs/state-of-the-art.md`. They record tested root sets, not format standards.
