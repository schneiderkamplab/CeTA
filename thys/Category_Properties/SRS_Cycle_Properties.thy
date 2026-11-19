theory SRS_Cycle_Properties
  imports Category_Specifications.SRS_Cycle_Spec
    Rewriting_Sequences_Properties
begin

lemma srs_cycle_nontermination_iff:
  "\<not> srs_cycle_terminates R \<longleftrightarrow>
    (\<exists>ws. \<forall>i. cycle_string_step R (ws i) (ws (Suc i)))"
  by (simp add: srs_cycle_terminates_def infinite_steps_iff)
end
