theory TRS_Conditional_Operational_Transfer
  imports TRS_Conditional_Embedding
begin
fun conditional_source where
  "conditional_source (CRewrite s t) = to_term s"
| "conditional_source (CReach s t) = to_term s"
fun conditional_phase :: "('f,'v) conditional_goal \<Rightarrow> nat" where
  "conditional_phase (CRewrite s t) = 0"
| "conditional_phase (CReach s t) = 1"

lemma evaluation_order:
  assumes order: "quasi_decreasing_order (to_conditional_rules R) S"
    and inf: "conditional_inference A R g gs"
    and index: "i < length gs"
    and prefix: "\<And>j. j<i \<Longrightarrow> conditional_success A R (gs!j)"
  shows "(conditional_source g,conditional_source (gs!i)) \<in> S \<or>
    (conditional_source g = conditional_source (gs!i) \<and>
      conditional_phase (gs!i) < conditional_phase g)"
  using inf index prefix
proof cases
  case (reflexive s)
  with index show ?thesis by simp
next
  case (transitive s u t)
  have cases: "i=0 \<or> i=1" using index transitive by auto
  have first: "i=1 \<Longrightarrow> (to_term s,to_term u) \<in> cstep (to_conditional_rules R)"
    using prefix[of 0] conditional_success_embedding[of A R "CRewrite s u"] transitive by simp
  have subset: "cstep (to_conditional_rules R) \<subseteq> S"
    using order unfolding quasi_decreasing_order_def by blast
  have smaller: "i=1 \<Longrightarrow> (to_term s,to_term u) \<in> S"
    using first subset by (meson subsetD)
  show ?thesis using cases smaller transitive by auto
next
  case (rule l r cs C sigma)
  have idx: "i < length cs" using index rule by simp
  obtain s t where cond: "cs!i = (s,t)" by (cases "cs!i") auto
  have previous: "\<forall>j<i.
      (fst ((map (\<lambda>(s,t). (to_term s,to_term t)) cs)!j) \<cdot> to_substitution sigma,
       snd ((map (\<lambda>(s,t). (to_term s,to_term t)) cs)!j) \<cdot> to_substitution sigma)
        \<in> (cstep (to_conditional_rules R))^*"
  proof (intro allI impI)
    fix j assume j: "j<i"
    have bound: "j < length cs" using j idx by simp
    have "conditional_goal_holds (to_conditional_rules R) (gs!j)"
      by (rule conditional_success_embedding[OF prefix[OF j]])
    then show "(fst ((map (\<lambda>(s,t). (to_term s,to_term t)) cs)!j) \<cdot> to_substitution sigma,
       snd ((map (\<lambda>(s,t). (to_term s,to_term t)) cs)!j) \<cdot> to_substitution sigma)
        \<in> (cstep (to_conditional_rules R))^*"
      by (simp add: rule bound split_beta)
  qed
  have member: "((to_term l,to_term r),map (\<lambda>(s,t). (to_term s,to_term t)) cs)
      \<in> to_conditional_rules R"
    unfolding to_conditional_rules_def
    using imageI[of "((l,r),cs)" R "\<lambda>((l,r),cs). ((to_term l,to_term r),map (\<lambda>(s,t). (to_term s,to_term t)) cs)"] rule by simp
  note calls = order[unfolded quasi_decreasing_order_def, THEN conjunct2,
    THEN conjunct2, THEN conjunct2, THEN conjunct2]
  have call: "(to_term l \<cdot> to_substitution sigma, to_term s \<cdot> to_substitution sigma) \<in> S"
    using calls[rule_format, of "to_term l" "to_term r"
      "map (\<lambda>(s,t). (to_term s,to_term t)) cs" i "to_substitution sigma"]
      member previous idx
    by (simp add: cond)
  have ctxt: "((to_context C)\<langle>to_term l \<cdot> to_substitution sigma\<rangle>,
       to_term l \<cdot> to_substitution sigma) \<in> S^="
    using ctxt_imp_supteq[of "to_context C" "to_term l \<cdot> to_substitution sigma",
      unfolded supteq_supt_conv] order
    by (auto simp: quasi_decreasing_order_def)
  have "((to_context C)\<langle>to_term l \<cdot> to_substitution sigma\<rangle>,
       to_term s \<cdot> to_substitution sigma) \<in> S"
    using ctxt call order by (auto simp: quasi_decreasing_order_def dest: transD)
  then show ?thesis by (simp add: rule idx cond)
qed

theorem conditional_operational_termination_transfer:
  assumes "quasi_decreasing (to_conditional_rules R)"
  shows "trs_conditional_operationally_terminates A R"
proof -
  obtain S where order: "quasi_decreasing_order (to_conditional_rules R) S"
    using assms by (auto simp: quasi_decreasing_def)
  let ?F = "\<lambda>g. (conditional_source g,conditional_phase g)"
  let ?W = "inv_image (S^-1 <*lex*> less_than) ?F"
  have wf: "wf ?W" using order
    by (intro wf_inv_image wf_lex_prod; auto simp: quasi_decreasing_order_def SN_iff_wf)
  have sub: "{(h,g). conditional_evaluation_step A R g h} \<subseteq> ?W"
  proof (rule subsetI)
    fix x assume "x \<in> {(h,g). conditional_evaluation_step A R g h}"
    then obtain g h gs i where x: "x=(h,g)" and inf: "conditional_inference A R g gs"
      and idx: "i < length gs" and pre: "\<And>j. j<i \<Longrightarrow> conditional_success A R (gs!j)"
      and h: "h=gs!i" by (auto simp: conditional_evaluation_step_def)
    from evaluation_order[OF order inf idx pre] show "x \<in> ?W"
      by (auto simp: x h inv_image_def lex_prod_def)
  qed
  have "wf {(h,g). conditional_evaluation_step A R g h}"
    by (rule wf_subset[OF wf sub])
  then show ?thesis
    by (simp add: trs_conditional_operationally_terminates_def no_infinite_steps_def
      wf_iff_no_infinite_down_chain)
qed
end
