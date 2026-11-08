---
type: Formal Specification
title: "TRS Context-sensitive: specification, concrete checking and trust boundary"
status: stable
---
# Context-sensitive review

The canonical property is absence of an infinite sequence of ranked,
context-sensitive rewrite steps on arbitrary terms, including nonground terms.
The review preserves the full declared signature. It does not redefine the
category to discard unused symbols. The concrete and serialized checker
connections compile with certificate assumptions disabled and no admitted proofs.
Final combined strict replay retains **1,890/1,890** protected root/polarity pairs across the four reviewed categories, including **110/110 CSR** (105 YES, five NO). All source, repeated-checker and exact guidance-receipt audits pass.

## Reading order and conventions

1. [Shared terms and ranked signatures](../thys/Category_Specifications/Spec/TRS_Spec_Base.thy).
2. [Canonical CSR specification](../thys/Category_Specifications/Spec/TRS_Context_Sensitive_Spec.thy).
3. [Examples](../thys/Category_Specifications/Spec/TRS_Context_Sensitive_Examples.thy).
4. [Term, context and step correspondence](../thys/Category_Specifications/Bridge/TRS_Context_Sensitive_Equivalence.thy).
5. [Concrete checker and serialized bridge](../thys/Category_Specifications/Context_Sensitive_Integrated/TRS_Context_Sensitive_Integrated.thy).

The [TermCOMP category](https://termination-portal.org/wiki/TRS_Contextsensitive)
asks for termination of every rewrite sequence respecting the replacement map.
The [ARI CSTRS definition](https://project-coco.uibk.ac.at/ARI/cstrs.php)
requires declared arities, strictly increasing positive replacement positions
within each arity, and the full map when an entry is omitted. ARI positions
start at one; the mathematical and native internal indices start at zero.
The root is always permitted. Every edge above a nested rewrite must be
permitted. Rules are arbitrary signature-correct term pairs; no extra
nonvariable-left-side or variable-preservation restriction is imposed.
Variables form an infinite supply; signatures need not contain constants.
The mathematical step relation ignores out-of-arity indices because they
cannot select an occurrence. The input boundary rejects such invalid maps.

`context_sensitive_step_iff` proves preservation and reflection of individual
steps. `trs_context_sensitive_terminates_iff` identifies the canonical property
with `SN (sig_step (to_signature A) (csstep mu (to_rules R)))`.
The negated equivalence and infinite-sequence characterization are proved too.
No checker theory is imported by the specification session.

## The signature issue and exact checker conclusions

The general CeTA CSR dispatcher concludes termination, or its negation, on
`funas_trs R`. That is the rule signature, which can be smaller than ARI's
explicit signature. The former bridge's equality premise was not automatically
justified by parsing an ARI file. Ferrum previously dropped unused declarations
from its operational map; that behavior is now removed.

[`CSR_Signature_Extension`](../thys/Category_Specifications/Context_Sensitive_Integrated/CSR_Signature_Extension.thy)
proves `csr_signature_extension`: if `funas_trs R` is contained in `F`,
`Trs.wf_trs R`, and `SN (sig_step F (csstep mu R))`, then
`SN (csstep mu R)`. It replaces maximal foreign-root subterms by variables and
combines termination of the resulting terms with termination of those subterms.
The rule condition means nonvariable left sides and no new right-side variables.
It is a condition of this auxiliary theorem, not of the category.

[`CSR_Global_Checker`](../thys/Category_Specifications/Context_Sensitive_Integrated/CSR_Global_Checker.thy)
discharges that condition inside the checker branches that need extension.
Other branches already prove unrestricted termination; GM rule-removal prefixes
use extension on the checked residual before transferring termination back.
`check_gm_csr_global_sound` covers every extended CSR proof constructor.
`csr_integrated_global_sound` includes the forbidden-pattern route and actual
integrated dispatch with certificate assumptions disabled. It concludes
unrestricted `SN (csstep (mu_of mu) (set Rs))`.

`trs_context_sensitive_bound_decision` now proves
`b iff trs_context_sensitive_terminates A (mu_of mu) R` from only:

- `standard_problem A R`;
- `set Rs = to_rules R`;
- concrete integrated CSR checker acceptance with assumptions disabled.

There is no signature-equality, proof-family or rule-shape premise on this
integrated theorem. Both YES and NO support unused declarations. The YES/NO
corollaries expose the respective conclusions. A negative witness on the rule
signature remains a negative witness on the containing declared signature.

`trs_context_sensitive_serialized_decision` composes this result with the
actual integrated parser result and `certify_proof_integrated False None None
None text = Certified`. The parser-result premise binds the precise input,
property, answer and certificate; the theorem does not formalize the ARI parser
or the external ARI/CPF comparison.

The previous unused-declaration restriction has been removed from Rust and the
independent Python audit. This does not claim checker or prover completeness.

## Parsing, dispatch and original-input binding

`ferrum cert check-csr ORIGINAL.ari CERTIFICATE.xml --answer yes|no --ceta CETA`
checks the original declared signature, every map (including unused symbols),
rule multisets modulo per-rule variable renaming, the CSR strategy, property
and decision. Auxiliary CPF symbols remain distinct from declared symbols.
Malformed or duplicate declarations, unsupported attributes, weak-rule costs,
undeclared applied symbols and arity/map mismatches are rejected. Explicit CSR
format and category metadata must agree. No directory heuristic supplies the
replacement map.

The native TPDB certification path and Python replay use the same boundary
requirements. The Python comparison is independent of Ferrum's parser.
Original input, CPF and checker identities are recorded and checked; the Rust
bound command checks a private immutable CPF copy and requires exact CERTIFIED
output with a successful exit. Certificate-only CeTA/Ferrum checking remains
separate and does not establish original-benchmark correspondence.

The exporter also preserves a declared map if an optional auxiliary symbol has
the same name. It no longer emits a duplicate entry that could overwrite the
source declaration. A native empty-system fixture with that collision is
exported and certified in the regression gate.

## Verification and remaining trust

Session `Category_Context_Sensitive_Integrated` and the standalone specification
session build with normal proof checking. The admission audit checks all four
concrete decision/YES/NO/serialized results and the new extension and integrated global theorems.
The dependency audit reports only the inherited mechanisms
`Regexp_Method.check_eqv` and `Types_To_Sets.cancel_type_definition`.
No new axioms or admissions are introduced. This is not a kernel-only claim.

The remaining trusted surfaces are ARI/CPF parsing and comparison, Isabelle's inherited oracle mechanisms,
code generation, Haskell/Rust compilation, runtime execution and artifact
provenance. The concrete operation-module contracts have been discharged;
there is no residual abstract-module hypothesis in the integrated results.
The existing unified CeTA executable and generated checking logic are unchanged
by this review. Production deployment and the full independent two-checker
release are separate.

## Original review verification

[Verification receipt](data/csr-category-review-20261108.json) records the exact
binaries, theory hashes, proofs, input preflight and replay artifacts. Seventeen
Rust parser/export tests, 34 Python root-audit tests, 12 replay-harness tests and
52 bound CLI cases pass. The native auxiliary-name collision fixture also
exports and certifies successfully. Documentation conformance passes in both
repositories.

Ferrum SHA-256: `6203558d8e514705a10854b26202dd1cc5ed839201bdc42e7e3e5d1b3daed98f`.
Unchanged unified CeTA SHA-256: `5d50333bdfdccb3c143cc499162311a5846eb44ebdbfe46d493fec35c2b42d85`.
Oracle SHA-256: `1610d2312ef7c7e8ef694e36a1e0181ccd423b7e4989e92b3d071c4c7cbfa12c`.

## 2026-11-08 coverage follow-up

[Verification receipt](data/coverage-closure-20261108.json) records both successful
Isabelle session builds and the final strict replay: **Relative 113/113**
(97 YES, 16 NO) and **CSR 110/110** (105 YES, five NO). Original-input audits,
repeated unchanged-unified-CeTA checks and complete guidance authorization pass.
No root is lost. The final binary passes five Rust binding tests, 36 independent
Python audit tests and 77 native CLI cases, including unused declarations across
all six CSR YES proof families present in the retained corpus. The 77 cases
include 25 Outermost regressions for the shared witness scanner.

CeTA formal commits are `437e04f` (CSR) and `e3146a7` (Relative); Ferrum runtime
commit is `b91d7aec`. The final O2 Ferrum hash is
`1fdc35718db4996d75c2ddda022e3fda3efd10883398db4d2ad3d9b7d80dcd37`.
The unified CeTA remains
`5d50333bdfdccb3c143cc499162311a5846eb44ebdbfe46d493fec35c2b42d85`;
the unchanged Equational-reviewed oracle remains
`42ccbba8daea6a3cc152c7a76cd5bfcd08c1193de8df5493376037cf608591e9`.
Artifacts are in Ferrum `target/coverage-closure-reviewed-2`; the first passing
replay and intermediate failed proof/test attempts are preserved. Baseline
solver settings, category workers and root/atom ceilings are retained.

CSR has no remaining unused-declaration guard. Relative direct ranked loops
need no extension condition; other unrestricted NO families still do, because
unconditional transfer is false. No unchecked semantic or module premise is
introduced. Native parsing/witness comparison, inherited Isabelle mechanisms,
code generation, compilers, runtime and artifact provenance remain trusted.
This is a focused retention gate, not checker completeness, production promotion
or the independent two-checker release.
