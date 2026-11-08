theory TRS_Relative_Equivalence
  imports Category_Specifications.TRS_Relative_Spec Rewriting_Sequence_Equivalence
begin

lemma standard_finite_steps_iff:
  "finite_steps (standard_step A R) s t \<longleftrightarrow>
    (to_term s,to_term t) \<in> (sig_step (to_signature A) (rstep (to_rules R)))^*"
proof -
  interpret step_translation to_term from_term "standard_step A R"
    "sig_step (to_signature A) (rstep (to_rules R))"
    by unfold_locales (simp_all add: standard_step_iff)
  show ?thesis by (rule finite_steps_iff)
qed

lemma relative_step_iff:
  "relative_step A R S s t \<longleftrightarrow> (to_term s,to_term t) \<in>
    relto (sig_step (to_signature A) (rstep (to_rules R)))
      (sig_step (to_signature A) (rstep (to_rules S)))"
  unfolding relative_step_def standard_finite_steps_iff standard_step_iff
  by (auto; metis to_from)

theorem trs_relative_terminates_iff_signature:
  "trs_relative_terminates A R S \<longleftrightarrow>
    SN_rel (sig_step (to_signature A) (rstep (to_rules R)))
      (sig_step (to_signature A) (rstep (to_rules S)))"
proof -
  interpret step_translation to_term from_term "relative_step A R S"
    "relto (sig_step (to_signature A) (rstep (to_rules R)))
      (sig_step (to_signature A) (rstep (to_rules S)))"
    by unfold_locales (simp_all add: relative_step_iff)
  show ?thesis by (simp only: trs_relative_terminates_def termination_iff SN_rel_defs)
qed

text \<open>Relative termination is not generally invariant under signature
extension. Either a symbol of arity at least two, or the variable condition on
weak rules, suffices. These are hypotheses of the bridge, not hidden changes
to the category definition.\<close>
definition relative_extension_condition where
  "relative_extension_condition A S \<longleftrightarrow>
    (\<exists>f n. A f = Some n \<and> n > 1) \<or>
    (\<forall>l r. (l,r) \<in> to_rules S \<longrightarrow> vars_term r \<subseteq> vars_term l)"

lemma ordinary_relative_implies_ranked:
  "SN_rel (rstep (to_rules R)) (rstep (to_rules S)) \<Longrightarrow> trs_relative_terminates A R S"
proof -
  have weak: "(sig_step (to_signature A) (rstep (to_rules S)))^* \<subseteq> (rstep (to_rules S))^*"
    by (rule rtrancl_mono) (auto simp: sig_step_def)
  have sub: "relto (sig_step (to_signature A) (rstep (to_rules R)))
    (sig_step (to_signature A) (rstep (to_rules S))) \<subseteq>
    relto (rstep (to_rules R)) (rstep (to_rules S))"
    using weak unfolding sig_step_def by blast
  show "SN_rel (rstep (to_rules R)) (rstep (to_rules S)) \<Longrightarrow> trs_relative_terminates A R S"
    unfolding trs_relative_terminates_iff_signature SN_rel_defs
    by (rule SN_subset[OF _ sub])
qed

theorem trs_relative_terminates_iff:
  assumes problem: "relative_problem A R S"
    and extension: "relative_extension_condition A S"
  shows "trs_relative_terminates A R S \<longleftrightarrow> SN_rel (rstep (to_rules R)) (rstep (to_rules S))"
proof
  assume sn: "trs_relative_terminates A R S"
  have F: "funas_trs (to_rules R) \<subseteq> to_signature A"
    "funas_trs (to_rules S) \<subseteq> to_signature A"
    using problem correct_rules unfolding relative_problem_def by blast+
  have restricted: "SN_rel (sig_step (to_signature A) (rstep (to_rules R)))
    (sig_step (to_signature A) (rstep (to_rules S)))"
    using sn by (simp add: trs_relative_terminates_iff_signature)
  from extension show "SN_rel (rstep (to_rules R)) (rstep (to_rules S))"
    unfolding relative_extension_condition_def
  proof
    assume "\<exists>f n. A f = Some n \<and> n > 1"
    then have "\<exists>f n. (f,n) \<in> to_signature A \<and> n > 1"
      by (auto simp: to_signature_def)
    then show ?thesis by (rule sig_ext_relative_rewriting_non_unary[OF _ F restricted])
  next
    assume "\<forall>l r. (l,r) \<in> to_rules S \<longrightarrow> vars_term r \<subseteq> vars_term l"
    then show ?thesis by (intro sig_ext_relative_rewriting_var_cond[OF _ F restricted]) blast
  qed
next
  show "SN_rel (rstep (to_rules R)) (rstep (to_rules S)) \<Longrightarrow> trs_relative_terminates A R S"
    by (rule ordinary_relative_implies_ranked)
qed
corollary trs_relative_nonterminates_iff:
  "relative_problem A R S \<Longrightarrow> relative_extension_condition A S \<Longrightarrow>
    (\<not> trs_relative_terminates A R S) \<longleftrightarrow> \<not> SN_rel (rstep (to_rules R)) (rstep (to_rules S))"
  by (simp add: trs_relative_terminates_iff)
end
