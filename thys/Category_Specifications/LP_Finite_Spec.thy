theory LP_Finite_Spec
  imports LP_Spec_Base
begin

text \<open>Definite logic programming with finite terms and an occurs check:
universal leftmost termination for the declared class of queries. A cyclic
unification equation has no finite solution.\<close>
definition lp_finite_terminates ::
  "'f arity \<Rightarrow> ('f,'v) logic_clause list \<Rightarrow> 'f \<Rightarrow> bool list \<Rightarrow> bool" where
  "lp_finite_terminates A P p modes \<longleftrightarrow> logic_terminates_in A logic_finite P p modes"

end
