# Integer transition-system checker

This component extends CeTA's existing LTS termination processors with exact
integer-state nontermination and binary CPF5 `div`/`mod` expressions. It is
exported from Isabelle; generated Haskell must never be edited.

The internal theory names retain their historical `ITS4`/`IA4` prefixes.
New certificates use CPF 5 XML. The unified `its` interface requires CPF 5/6;
`--legacy` explicitly enables historical CPF 3/4 ITS certificates. Inherited
CPF3 LTS proofs also remain available through the ordinary `cpf` interface.

`ITS4_Parser.check_its4_sound` connects the top-level YES/NO dispatch to LTS
termination. Termination uses the existing cooperation, ranking, invariant,
location-addition, and fresh-variable theorems, instantiated over the extended
integer signature. Nontermination supports ground loops, recurrent regions, and recurrent cycles.
Ground loops check an initial total valuation, a reachable stem, and a nonempty
loop returning to the identical total state. Recurrent proofs instead check
reachability and preservation of a region using explicit typed successor
policies; satisfiability or an abstract cycle alone is insufficient.
The corresponding theories are `IA4_Nontermination`, `IA4_Recurrent`, and
`IA4_Recurrent_Cycle`.

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
Symbolic divisors remain unsupported. Recurrent-region and recurrent-cycle
coverage is exactly that of the checked policy obligations above; this does
not claim general acceleration or arbitrary nonlinear recurrence reasoning.

LeTA's independent Lean implementation lives in `CeTA-Lean/CetaLean/ITS` in
the sibling repository. Its unified executable currently checks ground loops,
recurrent regions, and recurrent cycles. The historical ITS NO replay certified
475 roots twice; 14 further roots are excluded by the strict ARI source parser
because they contain empty rule argument lists. Arithmetic validity and ranking
removal have Lean soundness proofs, but the full cooperation-based YES checker
is still under development. This is not yet CeTA/LeTA ITS coverage parity.
See `CeTA-Lean/docs/state-local-integration.md` and its replay evidence for the
precise gates. LeTA does not call CeTA or trust a prover's verdict.
