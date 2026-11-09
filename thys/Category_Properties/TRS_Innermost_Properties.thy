theory TRS_Innermost_Properties
  imports Category_Specifications.TRS_Innermost_Spec
    TRS_Properties
begin

lemma trs_innermost_nontermination_iff:
  "\<not> trs_innermost_terminates A R \<longleftrightarrow>
    (\<exists>ts. \<forall>i. innermost_step A R (ts i) (ts (Suc i)))"
  by (simp add: trs_innermost_terminates_def no_infinite_steps_def)
end
