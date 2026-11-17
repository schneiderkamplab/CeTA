theory LP_Cut_Infinite_Spec
  imports LP_Cut_Spec_Base
begin

text \<open>This separate variant permits arbitrary, possibly non-rational,
infinite runtime trees. Program clauses and initial queries remain finite.
Unification is still most general within this domain. This property is not
identified with finite-term or rational-tree termination.\<close>
definition lp_cut_infinite_terminates ::
  "'f arity \<Rightarrow> ('f,'v) logic_cut_program \<Rightarrow> 'f \<Rightarrow> bool list \<Rightarrow> bool" where
  "lp_cut_infinite_terminates A P p modes \<longleftrightarrow> logic_cut_terminates_in A (\<lambda>_. True) P p modes"

end
