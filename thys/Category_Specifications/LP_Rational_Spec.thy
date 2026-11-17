theory LP_Rational_Spec
  imports LP_Spec_Base
begin

text \<open>The separate no-occurs-check variant permits rational runtime trees.
Initial queries and program clauses are still finite. This is not a definition
of full Prolog, nor a quantification over arbitrary non-rational infinite trees.\<close>
definition lp_rational_terminates ::
  "'f arity \<Rightarrow> ('f,'v) logic_clause list \<Rightarrow> 'f \<Rightarrow> bool list \<Rightarrow> bool" where
  "lp_rational_terminates A P p modes \<longleftrightarrow> logic_terminates_in A logic_rational P p modes"

end
