theory TRS_Conditional_Ordinary_Spec
  imports TRS_Conditional_Spec_Base
begin
text \<open>Ordinary termination excludes infinite sequences of completed
conditional rewrites on arbitrary signature-correct terms, including open terms.\<close>
definition trs_conditional_terminates where
  "trs_conditional_terminates A R \<longleftrightarrow> no_infinite_steps (conditional_step A R)"
lemma trs_conditional_nontermination_iff:
  "\<not> trs_conditional_terminates A R \<longleftrightarrow>
    (\<exists>ts. \<forall>i. conditional_step A R (ts i) (ts (Suc i)))"
  by (simp add: trs_conditional_terminates_def no_infinite_steps_def)
end
