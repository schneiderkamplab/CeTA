---
type: Formal Specification
title: "TRS Innermost: strict integrated checking and trust boundary"
status: draft
---
# TRS Innermost: strict integrated checking and trust boundary

This review follows [Standard](trs-standard-trust-boundary.md). Read the
[canonical definition and equivalences](trs-innermost-specification.md) first,
then the [concrete checker composition](../thys/Category_Bridges/Innermost_Integrated/TRS_Innermost_Integrated.thy).
Human approval is not recorded by a successful build.

## Category and exact configuration

The [TPDB category definition](https://termination-portal.org/wiki/Term_Rewriting)
permits arbitrary term pairs and arbitrary starting terms. Innermost contracts
an instance only when every proper subterm is normal. There is no groundness,
left-to-right, constant-symbol, nonvariable-left-side, or right-variable restriction.
The ranked signature and declarations are checked. Ordinary ARI TRS syntax does
not supply a strategy declaration: the explicitly selected category supplies it;
recognized TPDB directory components must agree. Unknown ARI declarations are
rejected, not interpreted as informal hints.

The bound certificate root must have exactly the ordinary TRS, no weak rules,
and `<strategy><innermost><nfs>false</nfs></innermost></strategy>`.
`false` disables the additional normal-form-substitution test; it does not
disable the innermost proper-subterm test. Both `true` and omission are rejected
at this boundary. Although CeTA defaults omission to false, the bound interface
requires the explicit flag. No rule-shape-based exception is made for true.
Internal proof transformations remain subject to the existing checker proofs.

## Exact theorem and discharged obligations

`trs_innermost_integrated_decision` states:

```text
trs_problem A R
set Rs = to_rules R
certify_integrated_cert_problem False
  (Inn_TRS_input (Innermost False) Rs []) Termination (Decision b) certificate = Certified
==> (b <-> trs_innermost_terminates A R)
```

`trs_innermost_integrated_YES` and `trs_innermost_integrated_NO` give the two
polarities. `trs_innermost_serialized_decision` uses the actual entry point
`certify_proof_integrated False None None None text`, with an explicit premise
that the production parser returns precisely that input/property/answer tuple.
The concrete checker soundness theorem discharges module correctness. No
`tp_spec`, `dpp_spec`, rule-shape condition, or nfs-equivalence assumption is
left for the caller. Certificate assumptions are disabled. No new axiom or
admitted proof is introduced.

The mathematical equivalence uses countable symbols and countably infinite
variables. The concrete string/label representation satisfies the countability
requirements; string variables provide the infinite supply. These are not
restrictions on finite ARI problems. Finiteness and arity correctness are input
validity conditions. Rule equality and parser agreement identify the problem
being checked; successful checker acceptance is the premise of soundness.
These necessary premises should not be confused with unproved processor claims.

## Bound runtime paths

```sh
ferrum cert check-innermost original.ari proof.xml --answer yes --ceta ../CeTA/ceta
```

Use `--answer no` for nontermination. The common Rust gate validates declarations,
category, root rules modulo per-rule variable renaming, injective quoted-symbol
aliases, strategy, termination property, and requested decision. The unchanged
unified CeTA checks a private copy of the same CPF bytes with assumptions disabled.
A successful receipt records original, CPF and checker SHA-256 identities;
observed changes during checking cause rejection.

Native TPDB certification checks category validity before dispatch and uses this
gate before counting Innermost certification. The replay harness independently
compares the original ARI and CPF and retains `innermost-input-binding.json`.
Direct CeTA and `cert check` still check the certificate's embedded problem only.
They are not substitutes for original-input binding.

Ordinary ARI and plain CPF root terms/rules are supported. Unsupported legacy
text TRS and indexed/marked root encodings are rejected. The existing loop-proof
constructor rejects variable-left-side loops, even though the category permits
those rules. This is a certificate-coverage limitation, not an assumption that
such TRSs terminate. The strict boundary also deliberately rejects older root
certificates containing `nfs=true`; regenerate them and check the new proof.

## Verification and remaining trust

Build using `make isabelle-trs-innermost-integrated ISABELLE=/path/to/isabelle
AFP="$AFP"`. The separate session preserves the lightweight specification session.
Examples cover empty and terminating systems, nonground rewriting below the root,
blocked outer redexes, a self-loop without constants, and arity mismatch.
The normal integrated build passed (55 seconds for the session, 76 seconds
overall), including inherited-admission checks. A separate process recorded
the inherited oracle names. Runtime checks passed 98 Innermost-focused Rust
tests, the category pre-dispatch regression, 19 independent correspondence
tests, 9 replay-harness tests, 11 Innermost CLI cases and 6 Standard CLI
regressions. Both repositories pass documentation conformance checks.
Verification results and retained source identities are recorded in the
[receipt](data/trs-innermost-integrated-verification-20261108.json).

The remaining trust boundary is the same as Standard: human agreement with the
category definition; tested but unverified ARI/XML parsers and correspondence
code; code generation, adapters, compiler/runtime and execution environment;
source-to-executable provenance; and Isabelle/HOL foundations including the
inherited `Regexp_Method.check_eqv` and `Types_To_Sets.cancel_type_definition`
oracles. In particular, runtime correspondence has not been formally proved to
imply the serialized theorem's parser premise. There is no claim of literally
assumption-free end-to-end execution, kernel-only checking, or checker completeness.
There are no remaining extra semantic or caller-supplied checker-module assumptions
for the concrete Innermost configuration above.

CeTA proof sources changed; generated checker logic and the installed unified
CeTA executable did not. A development Ferrum binary exercises the tightened
source paths. Production binary promotion and full-frontier replay are outside
this milestone, so no production deployment or replay improvement is claimed.
