theory LP_Rational_Spec
  imports LP_Spec_Base
begin

text \<open>The separate no-occurs-check variant permits rational runtime trees.
Initial queries and program clauses are still finite. This is not a definition
of full Prolog, nor a quantification over arbitrary non-rational infinite trees.\<close>
definition lp_rational_terminates where
  "lp_rational_terminates P p modes \<longleftrightarrow> logic_terminates_in logic_rational P p modes"

end
