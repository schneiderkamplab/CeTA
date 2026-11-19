theory TRS_Conditional_Closure
  imports TRS_Conditional_Witnesses
begin
fun native_goal_subst where
  "native_goal_subst sigma (b,s,t) = (b,s \<cdot> sigma,t \<cdot> sigma)"

lemma signature_subst:
  "funas_term t \<subseteq> F \<Longrightarrow> (\<forall>x. funas_term (sigma x) \<subseteq> F) \<Longrightarrow>
    funas_term (t \<cdot> sigma) \<subseteq> F"
  by (auto simp: funas_term_subst)

lemma native_inference_subst:
  assumes inf: "native_conditional_inference F R g gs"
    and sig: "\<forall>x. funas_term (tau x) \<subseteq> F"
  shows "native_conditional_inference F R (native_goal_subst tau g) (map (native_goal_subst tau) gs)"
  using inf
proof cases
  case (reflexive s)
  then show ?thesis using signature_subst[OF _ sig]
    by (simp add: native_conditional_inference.reflexive)
next
  case (transitive s u t)
  then show ?thesis using signature_subst[OF _ sig]
    by (simp add: native_conditional_inference.transitive)
next
  case (apply_rule l r cs C sigma)
  have mem: "((l,r),cs) \<in> R" using apply_rule by simp
  have ctx: "funas_ctxt (C \<cdot>\<^sub>c tau) \<subseteq> F" using apply_rule sig by auto
  have sub: "\<forall>x. funas_term ((sigma \<circ>\<^sub>s tau) x) \<subseteq> F"
    using apply_rule sig by (auto simp: subst_compose funas_term_subst)
  have wf: "funas_term ((C\<langle>l \<cdot> sigma\<rangle>) \<cdot> tau) \<subseteq> F"
    "funas_term ((C\<langle>r \<cdot> sigma\<rangle>) \<cdot> tau) \<subseteq> F"
    using apply_rule sig by (auto simp: subst_compose funas_term_subst)
  have cswf: "\<forall>(s,t)\<in>set cs. funas_term (s \<cdot> (sigma \<circ>\<^sub>s tau)) \<subseteq> F \<and>
      funas_term (t \<cdot> (sigma \<circ>\<^sub>s tau)) \<subseteq> F"
    using apply_rule sig by (auto simp: funas_term_subst split: prod.splits)
  show ?thesis
    using native_conditional_inference.apply_rule[OF mem ctx sub] apply_rule wf cswf
    by (simp add: map_map split_def o_def)
qed

lemma native_success_subst:
  assumes "native_conditional_success F R g" "\<forall>x. funas_term (tau x) \<subseteq> F"
  shows "native_conditional_success F R (native_goal_subst tau g)"
  using assms(1)
proof (induct rule: native_conditional_success.induct)
  case (conclude g gs)
  have inf: "native_conditional_inference F R (native_goal_subst tau g) (map (native_goal_subst tau) gs)"
    by (rule native_inference_subst[OF conclude.hyps(1) assms(2)])
  show ?case by (rule native_conditional_success.conclude[OF inf])
    (use conclude in \<open>simp add: list_all_iff\<close>)
qed
lemma ranked_cstep_subst:
  "(s,t) \<in> ranked_cstep F R \<Longrightarrow> (\<forall>x. funas_term (sigma x) \<subseteq> F) \<Longrightarrow>
    (s \<cdot> sigma,t \<cdot> sigma) \<in> ranked_cstep F R"
  using native_success_subst[of F R "(False,s,t)" sigma]
  by (simp add: ranked_cstep_def)
end
