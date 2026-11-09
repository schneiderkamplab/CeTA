theory TRS_Relative_Properties
  imports Category_Specifications.TRS_Relative_Spec
    TRS_Properties
begin

lemma trs_relative_nontermination_iff:
  "\<not> trs_relative_terminates A R S \<longleftrightarrow>
    (\<exists>ts. \<forall>i. relative_step A R S (ts i) (ts (Suc i)))"
  by (simp add: trs_relative_terminates_def infinite_steps_iff)
end
