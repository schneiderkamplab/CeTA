theory LP_Cut_Rational_Spec
  imports LP_Cut_Spec_Base
begin

text \<open>Universal termination of the ordered cut machine with rational
runtime terms. Clause order, backtracking, scope and query modes are retained.\<close>
definition lp_cut_rational_terminates where
  "lp_cut_rational_terminates P p modes \<longleftrightarrow> logic_cut_terminates_in logic_rational P p modes"

end
