theory LP_Finite_Spec
  imports LP_Spec_Base
begin

text \<open>Definite logic programming with finite terms and an occurs check:
universal leftmost termination for the declared class of queries. A cyclic
unification equation has no finite solution.\<close>
definition lp_finite_terminates where
  "lp_finite_terminates P p modes \<longleftrightarrow> logic_terminates_in logic_finite P p modes"

end
