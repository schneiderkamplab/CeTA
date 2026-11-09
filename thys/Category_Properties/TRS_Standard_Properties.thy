theory TRS_Standard_Properties
  imports Category_Specifications.TRS_Standard_Spec
    TRS_Properties
begin

lemma trs_standard_nontermination_iff:
  "\<not> trs_standard_terminates A R \<longleftrightarrow>
    (\<exists>ts. \<forall>i. fo_step A R (ts i) (ts (Suc i)))"
  by (simp add: trs_standard_terminates_def no_infinite_steps_def)
end
