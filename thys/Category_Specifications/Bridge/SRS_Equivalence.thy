theory SRS_Equivalence
  imports Category_Specifications.SRS_Standard_Spec
    Category_Specifications.SRS_Relative_Spec
    Rewriting_Sequence_Equivalence Not_SN.Nonloop_SRS
begin
text \<open>Both representations use HOL lists, so the word and rule translations
are identities. The replacement relation is nevertheless proved equivalent
in both directions.\<close>
lemma string_step_iff:
  "string_step R s t \<longleftrightarrow> (s,t) \<in> srs_step R"
proof
  assume "string_step R s t"
  then show "(s,t) \<in> srs_step R"
    unfolding string_step_def by (auto intro: srs_step.step)
next
  assume "(s,t) \<in> srs_step R"
  then show "string_step R s t"
    by (cases rule: srs_step.cases) (auto simp: string_step_def)
qed

lemma string_finite_steps_iff:
  "finite_steps (string_step R) s t \<longleftrightarrow> (s,t) \<in> (srs_step R)^*"
  unfolding finite_steps_relation string_step_iff by simp

theorem srs_standard_terminates_iff:
  "srs_standard_terminates R \<longleftrightarrow> SN (srs_step R)"
  unfolding srs_standard_terminates_def no_infinite_steps_def string_step_iff SN_defs by blast
lemma relative_string_step_iff:
  "relative_string_step R S s t \<longleftrightarrow> (s,t) \<in> relto (srs_step R) (srs_step S)"
  unfolding relative_string_step_def string_finite_steps_iff string_step_iff by blast

theorem srs_relative_terminates_iff:
  "srs_relative_terminates R S \<longleftrightarrow> SN_rel (srs_step R) (srs_step S)"
  unfolding srs_relative_terminates_def no_infinite_steps_def relative_string_step_iff SN_rel_defs SN_defs by blast

corollary srs_standard_nonterminates_iff:
  "(\<not> srs_standard_terminates R) \<longleftrightarrow> \<not> SN (srs_step R)"
  by (simp add: srs_standard_terminates_iff)
corollary srs_relative_nonterminates_iff:
  "(\<not> srs_relative_terminates R S) \<longleftrightarrow> \<not> SN_rel (srs_step R) (srs_step S)"
  by (simp add: srs_relative_terminates_iff)
end
