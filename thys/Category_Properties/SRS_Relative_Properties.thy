theory SRS_Relative_Properties
  imports Category_Specifications.SRS_Relative_Spec
    Rewriting_Sequences_Properties
begin

lemma srs_relative_nontermination_iff:
  "\<not> srs_relative_terminates R S \<longleftrightarrow>
    (\<exists>ws. \<forall>i. relative_string_step R S (ws i) (ws (Suc i)))"
  by (simp add: srs_relative_terminates_def infinite_steps_iff)
end
