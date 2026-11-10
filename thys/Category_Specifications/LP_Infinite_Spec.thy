theory LP_Infinite_Spec
  imports LP_Spec_Base
begin

text \<open>This separate variant permits arbitrary, possibly non-rational,
infinite runtime trees. Program clauses and initial queries remain finite.
Unification is still most general within this domain. This property is not
identified with finite-term or rational-tree termination.\<close>
definition lp_infinite_terminates where
  "lp_infinite_terminates P p modes \<longleftrightarrow> logic_terminates_in (\<lambda>_. True) P p modes"

end
