theory TRS_Conditional_Ordinary_Spec
  imports TRS_Conditional_Spec_Base
begin
text \<open>Ordinary termination excludes infinite sequences of completed
conditional rewrites on arbitrary signature-correct terms, including open terms.\<close>
definition trs_conditional_terminates where
  "trs_conditional_terminates A R \<longleftrightarrow> no_infinite_steps (conditional_step A R)"
end
