theory Relative_ADP_Global
  imports Relative_ADP_Block_Dev.Relative_ADP_Block
begin

lemma adp_step_case_mono:
  assumes subset: "P \<subseteq> P'"
    and step: "adp_step_case P at_sharp s t"
  shows "adp_step_case P' at_sharp s t"
  using step
proof cases
  case (adp_stepI l r phi p sigma A)
  show ?thesis
    by (rule adp_step_case.adp_stepI[OF subset[THEN subsetD, OF adp_stepI(1)]
          adp_stepI(2-8)])
qed

lemma adp_step_case_rel_mono:
  assumes "P \<subseteq> P'"
  shows "adp_step_case_rel P at_sharp \<subseteq> adp_step_case_rel P' at_sharp"
  using adp_step_case_mono[OF assms]
  unfolding adp_step_case_rel_def by blast

lemma adp_step_mono:
  assumes "P \<subseteq> P'"
  shows "adp_step P \<subseteq> adp_step P'"
  unfolding adp_step_def
  using adp_step_case_rel_mono[OF assms, where at_sharp = True]
    adp_step_case_rel_mono[OF assms, where at_sharp = False]
  by blast

lemma adp_productive_block_rel_subset_relto:
  "adp_productive_block_rel P Q \<subseteq>
    relto (adp_step_case_rel P True) (adp_step (P \<union> Q))"
proof
  fix st
  assume "st \<in> adp_productive_block_rel P Q"
  then obtain s t u where st: "st = (s, u)"
    and weak: "(s, t) \<in> (adp_step (P \<union> Q))\<^sup>*"
    and strict: "(t, u) \<in> adp_step_case_rel P True"
    unfolding adp_productive_block_rel_def by blast
  show "st \<in> relto (adp_step_case_rel P True) (adp_step (P \<union> Q))"
    unfolding st
    using weak strict by blast
qed

lemma serial_productive_blocks_not_SN:
  fixes X :: "('f adp_symbol, 'v) term set"
  assumes start: "s0 \<in> X"
    and progress: "\<And>s. s \<in> X \<Longrightarrow>
      \<exists>t. t \<in> X \<and> (s, t) \<in> adp_productive_block_rel P Q"
  shows "\<not> adp_problem_SN (P, Q)"
proof -
  obtain f where f0: "f 0 = s0"
    and fX: "\<And>n. f n \<in> X"
    and blocks: "\<And>n. (f n, f (Suc n)) \<in> adp_productive_block_rel P Q"
    using dependent_nat_choice_start[of "\<lambda>_ s. s \<in> X" s0
        "\<lambda>_ s t. (s, t) \<in> adp_productive_block_rel P Q"]
      start progress by metis
  have chain_blocks: "chain (adp_productive_block_rel P Q) f"
    using blocks unfolding chain_def by blast
  have chain_relto:
      "chain (relto (adp_step_case_rel P True) (adp_step (P \<union> Q))) f"
    by (rule chain_mono[OF adp_productive_block_rel_subset_relto chain_blocks])
  have "\<not> SN_on
      (relto (adp_step_case_rel P True) (adp_step (P \<union> Q))) UNIV"
    by (rule not_SN_onI[OF _ chain_relto]) simp
  then show ?thesis
    unfolding adp_problem_SN_def SN_rel_on_def by simp
qed

end
