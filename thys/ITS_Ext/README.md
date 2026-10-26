# Integer transition-system checker

This component extends CeTA's existing LTS termination processors with exact
integer-state nontermination and binary CPF4 `div`/`mod` expressions. It is
exported from Isabelle; generated Haskell must never be edited.

`ITS4_Parser.check_its4_sound` connects the top-level YES/NO dispatch to LTS
termination. Termination uses the existing cooperation, ranking, invariant,
location-addition, and fresh-variable theorems, instantiated over the extended
integer signature. Nontermination checks an initial total valuation, a reachable
stem, and a nonempty loop returning to the identical total state.

`IA_Div_Mod` proves Euclidean existence and uniqueness for every nonzero signed
integer divisor. `IA4_Normalization` proves typing, evaluation preservation,
and satisfaction of fresh quotient/remainder constraints for nested arithmetic.
`IA4_Checker.elimination_sound` transfers validity from CeTA's existing integer
arithmetic checker. The CPF parser accepts only closed, nonzero divisors;
zero and symbolic divisors are explicit errors. No external solver is trusted
by this checker. Unlisted state coordinates denote zero (integer) or false
(Boolean); Ferrum emits all coordinates explicitly.

Build with `scripts/build_its_checker.sh NEW_OUTPUT_DIRECTORY`. Set `AFP` and
`ISABELLE_TOOL` for the installed Isabelle2025-2/AFP dependencies. Optional
`ITS_ISABELLE_USER_HOME` and `ITS_ISABELLE_IDENTIFIER` select an isolated cache
of previously checked dependency heaps. The build writes the executable,
unaltered Isabelle exports, source hashes, checker hashes, and build logs.

The `ITS_Ground` parent retains the original integer-only instance as a separate
integration test. `ITS_Arithmetic` contains the arithmetic proofs;
`ITS_Ext` instantiates the processors and exports the combined checker.
Symbolic divisors, recurrent sets, acceleration, and nonlinear recurrence
reasoning are outside this component's certified scope.
