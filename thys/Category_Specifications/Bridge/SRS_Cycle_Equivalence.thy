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

text \<open>Unused letters do not affect termination. Erasing letters outside
an alphabet containing both sides of every rule preserves each genuine step,
even when that alphabet is empty. Thus the unrestricted checker symbol type
introduces no signature-extension assumption.\<close>
lemma cycle_filter_step:
  assumes rules: "\<And>l r. (l,r) \<in> R \<Longrightarrow> list_all P l \<and> list_all P r"
    and step: "cycle_string_step R s t"
  shows "cycle_string_step R (filter P s) (filter P t)"
proof -
  obtain a b c d l r u v where
    st: "s = a @ b" "t = d @ c"
    and rule: "(l,r) \<in> R"
    and eq: "b @ a = u @ l @ v" "c @ d = u @ r @ v"
    using step unfolding cycle_string_step_def string_step_def by blast
  have fixed: "filter P l = l" "filter P r = r"
    using rules[OF rule] by (simp_all add: list_all_iff filter_id_conv)
  have eq': "filter P b @ filter P a = filter P u @ l @ filter P v"
    "filter P c @ filter P d = filter P u @ r @ filter P v"
    using arg_cong[OF eq(1), of "filter P"] arg_cong[OF eq(2), of "filter P"]
    by (simp_all add: fixed)
  have inner: "string_step R (filter P b @ filter P a) (filter P c @ filter P d)"
    unfolding string_step_def using rule eq' by blast
  show ?thesis unfolding cycle_string_step_def
    using inner st by (metis filter_append)
qed

theorem srs_cycle_nontermination_over_alphabet:
  assumes "\<And>l r. (l,r) \<in> R \<Longrightarrow> list_all P l \<and> list_all P r"
  shows "\<not> srs_cycle_terminates R \<longleftrightarrow>
    (\<exists>ws. \<forall>i. list_all P (ws i) \<and> cycle_string_step R (ws i) (ws (Suc i)))"
proof
  assume "\<not> srs_cycle_terminates R"
  then obtain ws where steps: "\<And>i. cycle_string_step R (ws i) (ws (Suc i))"
    using srs_cycle_nontermination_iff by blast
  show "\<exists>ws. \<forall>i. list_all P (ws i) \<and> cycle_string_step R (ws i) (ws (Suc i))"
    by (intro exI[of _ "\<lambda>i. filter P (ws i)"] allI conjI)
      (auto simp: list_all_iff intro: cycle_filter_step[OF assms steps])
next
  assume "\<exists>ws. \<forall>i. list_all P (ws i) \<and> cycle_string_step R (ws i) (ws (Suc i))"
  then show "\<not> srs_cycle_terminates R" using srs_cycle_nontermination_iff by blast
qed
end
