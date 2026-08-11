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

definition erase_annotations_adp ::
  "('f, 'v) adp \<Rightarrow> ('f, 'v) adp" where
  "erase_annotations_adp p =
    (plain_adp_term (erase_adp_term (fst p)),
     plain_adp_term (erase_adp_term (snd p)))"

lemma erase_erase_annotations_adp [simp]:
  "erase_adp (erase_annotations_adp p) = erase_adp p"
  by (cases p) (simp add: erase_annotations_adp_def erase_adp_def)

lemma adp_step_case_union:
  "adp_step_case (P \<union> Q) at_sharp s t \<longleftrightarrow>
    adp_step_case P at_sharp s t \<or> adp_step_case Q at_sharp s t"
proof
  assume "adp_step_case (P \<union> Q) at_sharp s t"
  then show "adp_step_case P at_sharp s t \<or>
      adp_step_case Q at_sharp s t"
  proof cases
    case (adp_stepI l r phi p sigma A)
    from adp_stepI(1) show ?thesis
    proof
      assume "(l,r) \<in> P"
      then show ?thesis
        using adp_stepI(2-8)
        by (metis adp_step_case.adp_stepI disjI1)
    next
      assume "(l,r) \<in> Q"
      then show ?thesis
        using adp_stepI(2-8)
        by (metis adp_step_case.adp_stepI disjI2)
    qed
  qed
next
  assume "adp_step_case P at_sharp s t \<or>
      adp_step_case Q at_sharp s t"
  then show "adp_step_case (P \<union> Q) at_sharp s t"
    by (metis Un_iff adp_step_case_mono subsetI)
qed

lemma adp_step_case_rel_union:
  "adp_step_case_rel (P \<union> Q) at_sharp =
    adp_step_case_rel P at_sharp \<union> adp_step_case_rel Q at_sharp"
  unfolding adp_step_case_rel_def
  using adp_step_case_union by blast

lemma adp_step_union:
  "adp_step (P \<union> Q) = adp_step P \<union> adp_step Q"
  unfolding adp_step_def adp_step_case_rel_union by blast

lemma adp_step_case_rel_subset_adp_step:
  "adp_step_case_rel P at_sharp \<subseteq> adp_step P"
  unfolding adp_step_def by (cases at_sharp) auto

lemma adp_step_difference_subset:
  "adp_step P - adp_step A \<subseteq> adp_step (P - A)"
proof -
  have "P = (P - A) \<union> (P \<inter> A)" by blast
  then have "adp_step P = adp_step (P - A) \<union> adp_step (P \<inter> A)"
    by (metis adp_step_union)
  moreover have "adp_step (P \<inter> A) \<subseteq> adp_step A"
    by (rule adp_step_mono) blast
  ultimately show ?thesis by blast
qed

lemma adp_step_case_difference_subset:
  "adp_step_case_rel P at_sharp - adp_step A \<subseteq>
    adp_step_case_rel (P - A) at_sharp"
proof -
  have "P = (P - A) \<union> (P \<inter> A)" by blast
  then have split: "adp_step_case_rel P at_sharp =
      adp_step_case_rel (P - A) at_sharp \<union>
      adp_step_case_rel (P \<inter> A) at_sharp"
    by (metis adp_step_case_rel_union)
  have "adp_step_case_rel (P \<inter> A) at_sharp \<subseteq> adp_step A"
    using adp_step_case_rel_mono[of "P \<inter> A" A at_sharp]
      adp_step_case_rel_subset_adp_step[of A at_sharp]
    by blast
  with split show ?thesis by blast
qed

lemma adp_step_erasure_into_order:
  assumes order: "ctxt.closed NS" "subst.closed NS"
    and orient: "erase_adp ` P \<subseteq> NS"
    and step: "(s,t) \<in> adp_step P"
  shows "(erase_adp_term s, erase_adp_term t) \<in> NS"
proof -
  from adp_step_erases[OF step]
  have "(erase_adp_term s, erase_adp_term t) \<in> rstep (erase_adp ` P)" .
  then show ?thesis
    by (rule set_mp[OF rstep_subset[OF order orient]])
qed

lemma relative_adp_erasure_reduction_pair:
  assumes redpair: "mono_redtriple_order S NS NST"
    and all_weak: "erase_adp ` (P \<union> B) \<subseteq> NS"
    and selected_strict: "erase_adp ` A \<subseteq> S"
    and residual: "adp_problem_SN
      (P - A, (B - A) \<union> erase_annotations_adp ` A)"
  shows "adp_problem_SN (P,B)"
proof (rule ccontr)
  interpret mono_redtriple_order S NS NST by (rule redpair)
  let ?R = "adp_step_case_rel P True"
  let ?W = "adp_step (P \<union> B)"
  let ?D = "adp_step A"
  let ?P' = "P - A"
  let ?B' = "(B - A) \<union> erase_annotations_adp ` A"
  assume not_sn: "\<not> adp_problem_SN (P,B)"
  then obtain as where deriv: "ideriv ?R ?W as"
    unfolding adp_problem_SN_def SN_rel_ideriv by auto

  have order_sn: "SN_rel S NS"
    unfolding SN_rel_defs
    by (rule SN_subset[OF compatible_SN'[OF compat_NS_S SN]], regexp)
  have selected_sn: "SN_rel ?D ?W"
  proof (rule SN_rel_hom[OF order_sn, where f = erase_adp_term])
    fix s t
    assume step: "(s,t) \<in> ?D"
    show "(erase_adp_term s, erase_adp_term t) \<in> S"
      by (rule adp_step_erasure_into_order[
            OF ctxt_S subst_S selected_strict step])
  next
    fix s t
    assume step: "(s,t) \<in> ?W"
    have "(erase_adp_term s, erase_adp_term t) \<in> NS"
      by (rule adp_step_erasure_into_order[
            OF ctxt_NS subst_NS all_weak step])
    then show "(erase_adp_term s, erase_adp_term t) \<in> S \<union> NS"
      by blast
  qed

  have no_selected_deriv:
    "\<not> ideriv (?D \<inter> (?R \<union> ?W)) ((?R \<union> ?W) - ?D) as"
  proof
    assume selected: "ideriv (?D \<inter> (?R \<union> ?W))
        ((?R \<union> ?W) - ?D) as"
    have "ideriv ?D ?W as"
    proof (rule ideriv_mono[OF _ _ selected])
      show "?D \<inter> (?R \<union> ?W) \<subseteq> ?D" by blast
      show "(?R \<union> ?W) - ?D \<subseteq> ?W"
        using adp_step_case_rel_subset_adp_step[of P True]
          adp_step_mono[of P "P \<union> B"] by blast
    qed
    with selected_sn show False unfolding SN_rel_ideriv by blast
  qed

  from ideriv_split[OF deriv no_selected_deriv]
  obtain i where tail: "ideriv (?R - ?D) (?W - ?D) (shift as i)"
    by blast
  have strict_tail: "?R - ?D \<subseteq> adp_step_case_rel ?P' True"
    by (rule adp_step_case_difference_subset)
  have weak_tail: "?W - ?D \<subseteq> adp_step (?P' \<union> ?B')"
  proof -
    have "?W - ?D \<subseteq> adp_step ((P \<union> B) - A)"
      by (rule adp_step_difference_subset)
    also have "... \<subseteq> adp_step (?P' \<union> ?B')"
      by (rule adp_step_mono) blast
    finally show ?thesis .
  qed
  have "ideriv (adp_step_case_rel ?P' True)
      (adp_step (?P' \<union> ?B')) (shift as i)"
    by (rule ideriv_mono[OF strict_tail weak_tail tail])
  moreover from residual have
      "\<not> (\<exists>xs. ideriv (adp_step_case_rel ?P' True)
        (adp_step (?P' \<union> ?B')) xs)"
    unfolding adp_problem_SN_def SN_rel_ideriv by simp
  ultimately show False by blast
qed

end
