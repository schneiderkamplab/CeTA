theory SRS_Cycle_Equivalence
  imports Category_Specifications.SRS_Cycle_Spec SRS_Equivalence
    Cycle_Checker.Cycle_Transport
begin
lemma cycle_string_step_iff:
  "cycle_string_step R s t \<longleftrightarrow> (s,t) \<in> cycle_step R"
  by (simp add: cycle_string_step_def cycle_step_def string_step_iff)
theorem srs_cycle_terminates_iff:
  "srs_cycle_terminates R \<longleftrightarrow> SN (cycle_step R)"
  unfolding srs_cycle_terminates_def no_infinite_steps_def cycle_string_step_iff SN_defs by blast
corollary srs_cycle_nonterminates_iff:
  "(\<not> srs_cycle_terminates R) \<longleftrightarrow> \<not> SN (cycle_step R)"
  by (simp add: srs_cycle_terminates_iff)
end
