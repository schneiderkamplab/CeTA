theory TRS_Conditional_Ordinary_Properties
  imports Category_Specifications.TRS_Conditional_Ordinary_Spec
    TRS_Conditional_Properties_Base
begin

lemma trs_conditional_nontermination_iff:
  "\<not> trs_conditional_terminates A R \<longleftrightarrow>
    (\<exists>ts. \<forall>i. conditional_step A R (ts i) (ts (Suc i)))"
  by (simp add: trs_conditional_terminates_def no_infinite_steps_def)
end
