# Frozen baseline coverage and minimization evidence

The 3,484 eligible root records induce 45,753 observed obligations: 44,810 HPC
counters and 943 structural observations. Identical supporter sets are grouped
into 3,331 constraints. All original obligation identifiers remain recorded in
`matrix.json.gz`; bit `i` of each `candidate_bits_hex` names candidate `i`.

`minimum-bound.smt2.gz` asks whether at most 207 roots cover those constraints.
The independently repeated solver result is `unsat`; `verification.json` records
the solver identity and hashes. The recorded 208-root choice was separately
checked to cover every obligation. No secondary time/size optimum is claimed.

To repeat the cardinality check with Z3:

```
gzip -dc docs/consolidation/coverage-baseline/minimum-bound.smt2.gz | z3 -in -smt2
```

The denominator and selected proof artifacts are in
`tests/certification/compact`. The remaining files retain candidate costs, source
positions, checker/theorem-name candidates, and explicit gaps. Runtime counters
do not execute Isabelle proofs. These artifacts do not establish complete
criterion coverage or exact nested P/Q/R/minimality/replacement-map semantics.
