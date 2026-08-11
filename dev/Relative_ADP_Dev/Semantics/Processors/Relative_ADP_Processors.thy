theory Relative_ADP_Processors
  imports Relative_ADP_Direct_Criterion_Dev.Relative_ADP_Direct_Criterion
begin

lemma adp_step_case_mono:
  assumes subset: "P \<subseteq> Q"
    and step: "adp_step_case P at_sharp s t"
  shows "adp_step_case Q at_sharp s t"
  using step
proof cases
  case (adp_stepI l r phi p sigma A)
  show ?thesis
    by (rule adp_step_case.adp_stepI[
          OF subsetD[OF subset adp_stepI(1)] adp_stepI(2-8)])
qed

lemma adp_step_case_rel_mono:
  assumes "P \<subseteq> Q"
  shows "adp_step_case_rel P at_sharp \<subseteq>
    adp_step_case_rel Q at_sharp"
  using adp_step_case_mono[OF assms]
  unfolding adp_step_case_rel_def by blast

lemma adp_step_mono:
  assumes "P \<subseteq> Q"
  shows "adp_step P \<subseteq> adp_step Q"
  unfolding adp_step_def
  using adp_step_case_rel_mono[OF assms, of True]
    adp_step_case_rel_mono[OF assms, of False]
  by blast

lemma adp_problem_SN_mono:
  assumes main: "P \<subseteq> P'"
    and all: "P \<union> B \<subseteq> P' \<union> B'"
    and finite: "adp_problem_SN (P', B')"
  shows "adp_problem_SN (P, B)"
  unfolding adp_problem_SN_def fst_conv snd_conv
  by (rule SN_rel_mono[
        OF adp_step_case_rel_mono[OF main]
          adp_step_mono[OF all]
          finite[unfolded adp_problem_SN_def fst_conv snd_conv]])

theorem relative_adp_move_base_to_main:
  assumes selected: "A \<subseteq> B"
    and finite: "adp_problem_SN (P \<union> A, B - A)"
  shows "adp_problem_SN (P, B)"
proof (rule adp_problem_SN_mono[OF _ _ finite])
  show "P \<subseteq> P \<union> A" by blast
  show "P \<union> B \<subseteq> (P \<union> A) \<union> (B - A)"
    using selected by blast
qed

end
