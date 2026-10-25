# Certificate formats across the production categories

This is the entry point for the certificate interfaces used by the fourteen
production categories, through logic programming with cut. It documents the
existing interfaces; it does not rename all native formats to CPF4 or extend
the XML schema merely by listing a category here.

## Format and semantics map

| Category | Certificate interface and reference | Required source context |
| --- | --- | --- |
| TRS Standard | [CPF3](cpf3.xsd), [local CPF4 extensions](CPF4.md) | Original rules, full rewriting |
| TRS Innermost | CPF with innermost strategy and strategy-switch proofs | Original rules and innermost strategy; Q contexts in intermediate DP states |
| TRS Contextsensitive | [CPF4 CSR extensions](CPF4.md#context-sensitive-rewriting) | Original rules, replacement map and signature |
| SRS Standard | String systems represented through the first-order CPF interfaces, including bounds/RFC | Original string rules and their first-order representation |
| TRS Relative | Relative CPF and [relative ADP integration](../thys/Relative_ADP/README.md) | Strict and weak rules, kept distinct |
| SRS Relative | Relative CPF, including [relative RFC extensions](CPF4.md#right-forward-closures) | Strict and weak string rules and their representation |
| TRS Outermost | CPF strategy/checked transformation interfaces | Original rules and outermost strategy, not unrestricted termination of an unrelated residual |
| TRS Equational | CPF interfaces and the supported equational checker path | Rewrite rules and equations, with the intended rewriting-modulo relation |
| SRS Cycle | [Native cycle certificates](../README), parsed by [Main_Cycle.hs](../src/Haskell/Main_Cycle.hs) | Original string rules; rewriting modulo rotation requires genuine rewrite progress |
| TRS Conditional (operational) | Supported CPF termination paths; [native conditional descent/loop certificates](../src/Haskell/Main_Conditional.hs) | Original ordered conditions; operational calls and condition evaluation matter |
| TRS Conditional (ordinary termination) | [Source-bound erasure XML](../src/Haskell/Main_Conditional_Ordinary.hs); native conditional loops in `--ordinary` mode | Original conditional rules; nontermination must establish actual conditional rewriting, not just divergent condition evaluation |
| Higher-order rewriting | Native typed certificates and [CeTA delegation XML](../thys/Higher_Order_CeTA_Code/Higher_Order_CeTA_Code.thy); [source-bound call expansion](../thys/Higher_Order_Call_Expansion/README.md) | Original typed signature and rules, binding/substitution and the declared higher-order relation |
| Logic programming | [TOCL09 source-bound XML entry point](../src/Haskell/Main_LP_TOCL09.hs), [Pi-DP XML](../thys/Logic_Programming/LP_PiDP_XML.thy), source nontermination interfaces | Original clauses, query pattern and resolution semantics; a translated TRS certificate alone is insufficient |
| Logic programming with cut | [Integrated XML dispatcher](../scripts/LP_Cut_Integrated_Main.hs), including [SEG/triples XML](../thys/Logic_Programming/LP_Cut_SEG_Triple_XML.thy) and [NO XML](../thys/Logic_Programming/LP_Cut_NO_XML.thy) | Original ordered clauses, cut control and query pattern; recursive Split and successful-prefix obligations |

This map identifies interface families, not a claim that every processor in
every family is supported by every binary. Production manifests pin the actual
checker executable and its hash. Follow the executable parser and its generated
checker for the exact accepted grammar and side conditions.

## CPF and native interfaces are distinct

[cpf4.xsd](cpf4.xsd) is the schema for this repository's CPF4 dialect, not a
universal schema for every certificate above. [CPF4.md](CPF4.md) describes its
CSR/RFC additions. A `cpfVersion` value does not turn a native certificate into
CPF, and XML syntax alone does not imply CPF compatibility. This repository's
version name is not evidence of adoption by an external standards body.

Cycle and conditional native front ends declare their constructor grammar in
the linked Haskell drivers. LP interfaces define XML parsing in Isabelle
`*_XML.thy` theories and export executable checks. Higher-order interfaces use
their typed native representations and, where applicable, checked delegation
to first-order proofs. There is not yet a common XSD covering these native
interfaces; these source definitions are the exact implementation references.

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
