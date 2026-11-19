theory SRS_Standard_Properties
  imports Category_Specifications.SRS_Standard_Spec
    Rewriting_Sequences_Properties
begin

lemma srs_standard_nontermination_iff:
  "\<not> srs_standard_terminates R \<longleftrightarrow>
    (\<exists>ws. \<forall>i. string_step R (ws i) (ws (Suc i)))"
  by (simp add: srs_standard_terminates_def infinite_steps_iff)
end
