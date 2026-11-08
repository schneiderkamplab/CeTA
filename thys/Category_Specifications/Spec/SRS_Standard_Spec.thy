theory SRS_Standard_Spec
  imports SRS_Spec_Base
begin
text \<open>Termination excludes every infinite sequence of word replacements.\<close>
definition srs_standard_terminates where
  "srs_standard_terminates R \<longleftrightarrow> no_infinite_steps (string_step R)"
lemma srs_standard_nontermination_iff:
  "\<not> srs_standard_terminates R \<longleftrightarrow>
    (\<exists>ws. \<forall>i. string_step R (ws i) (ws (Suc i)))"
  by (simp add: srs_standard_terminates_def infinite_steps_iff)
end
