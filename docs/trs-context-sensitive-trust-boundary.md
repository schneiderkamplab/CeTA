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

`csr_direct_integrated_sound` proves that acceptance of the concrete direct CSR
proof language establishes unrestricted `SN (csstep mu R)`. It instantiates
`check_csr_termination_proof_min_sound` with the actual production modules.
This includes the direct empty-system, rule-removal and direct dependency-pair
constructors; it is not a theorem about every extended CSR proof constructor.

`trs_context_sensitive_bound_decision` proves
`b iff trs_context_sensitive_terminates A (mu_of mu) R` from:

- a finite signature-correct rule set over the actual infinite variable type;
- exact equality between the parsed rules and translated specification rules;
- acceptance by `certify_integrated_cert_problem False` of the CSR input,
  termination property and decision `b`;
- the checked `csr_signature_guard`.

The guard is automatically true for NO. For YES it requires either the declared
signature to equal the rule signature, or a direct CSR certificate. Rust and
the independent Python audit implement this guard. They never treat it as an
unchecked premise. `trs_context_sensitive_bound_YES` and
`trs_context_sensitive_bound_NO` expose the two conclusions; NO has no extra
signature-equality condition. A negative witness on the rule signature remains
a negative witness on a containing declared signature.

`trs_context_sensitive_serialized_decision` composes this result with the
actual integrated parser result and `certify_proof_integrated False None None
None text = Certified`. The parser-result premise binds the precise input,
property, answer and certificate; the theorem does not formalize the ARI parser
or the external ARI/CPF comparison.

**Coverage limit:** a general signature-extension theorem for the other CSR
proof languages has not been proved here. Their YES certificates on inputs
with unused declarations are rejected by the bound interface. The specification
is unchanged, and no unconditional equivalence is asserted to avoid this limit.
There is no claim that the checker or prover is complete.

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
concrete decision/YES/NO/serialized results and the stronger direct theorem.
The dependency audit reports only the inherited mechanisms
`Regexp_Method.check_eqv` and `Types_To_Sets.cancel_type_definition`.
No new axioms or admissions are introduced. This is not a kernel-only claim.

The remaining trusted surfaces are ARI/CPF parsing and comparison, enforcement
of the proof-shape/signature guard, Isabelle's inherited oracle mechanisms,
code generation, Haskell/Rust compilation, runtime execution and artifact
provenance. The concrete operation-module contracts have been discharged;
there is no residual abstract-module hypothesis in the integrated results.
The existing unified CeTA executable and generated checking logic are unchanged
by this review. Production deployment and the full independent two-checker
release are separate.

## Recorded verification

[Verification receipt](data/csr-category-review-20261108.json) records the exact
binaries, theory hashes, proofs, input preflight and replay artifacts. Seventeen
Rust parser/export tests, 34 Python root-audit tests, 12 replay-harness tests and
52 bound CLI cases pass. The native auxiliary-name collision fixture also
exports and certifies successfully. Documentation conformance passes in both
repositories.

Ferrum SHA-256: `6203558d8e514705a10854b26202dd1cc5ed839201bdc42e7e3e5d1b3daed98f`.
Unchanged unified CeTA SHA-256: `5d50333bdfdccb3c143cc499162311a5846eb44ebdbfe46d493fec35c2b42d85`.
Oracle SHA-256: `1610d2312ef7c7e8ef694e36a1e0181ccd423b7e4989e92b3d071c4c7cbfa12c`.
