theory TRS_Outermost_Properties
  imports Category_Specifications.TRS_Outermost_Spec
    TRS_Properties
begin

lemma trs_outermost_nontermination_iff:
  "\<not> trs_outermost_terminates A R \<longleftrightarrow>
    (\<exists>ts. \<forall>i. outermost_step A R (ts i) (ts (Suc i)))"
  by (simp add: trs_outermost_terminates_def no_infinite_steps_def)
end
