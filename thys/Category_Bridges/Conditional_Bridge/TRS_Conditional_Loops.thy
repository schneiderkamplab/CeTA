theory TRS_Conditional_Loops
  imports TRS_Conditional_Closure
begin
lemma ranked_path_context:
  assumes "(s,t) \<in> (ranked_cstep F R)^+" "funas_ctxt C \<subseteq> F"
  shows "(C\<langle>s\<rangle>,C\<langle>t\<rangle>) \<in> (ranked_cstep F R)^+"
  using assms(1)
  by (induct rule: trancl_induct) (meson ranked_cstep_context[OF _ assms(2)] r_into_trancl trancl_trans)+
lemma ranked_path_subst:
  assumes "(s,t) \<in> (ranked_cstep F R)^+" "\<forall>x. funas_term (sigma x) \<subseteq> F"
  shows "(s \<cdot> sigma,t \<cdot> sigma) \<in> (ranked_cstep F R)^+"
  using assms(1)
  by (induct rule: trancl_induct) (meson ranked_cstep_subst[OF _ assms(2)] r_into_trancl trancl_trans)+

fun ranked_loop_iterate where
  "ranked_loop_iterate C sigma 0 s = s"
| "ranked_loop_iterate C sigma (Suc n) s = C\<langle>ranked_loop_iterate C sigma n s \<cdot> sigma\<rangle>"
lemma ranked_loop_iterate_end:
  "ranked_loop_iterate C sigma n (C\<langle>s \<cdot> sigma\<rangle>) = ranked_loop_iterate C sigma (Suc n) s"
  by (induct n) simp_all

lemma ranked_context_substitution_loop:
  assumes path: "(s,C\<langle>s \<cdot> sigma\<rangle>) \<in> (ranked_cstep F R)^+"
    and ctx: "funas_ctxt C \<subseteq> F"
    and sub: "\<forall>x. funas_term (sigma x) \<subseteq> F"
  shows "\<not> SN (ranked_cstep F R)"
proof -
  have lift: "(ranked_loop_iterate C sigma n s,ranked_loop_iterate C sigma n t) \<in> (ranked_cstep F R)^+"
    if "(s,t) \<in> (ranked_cstep F R)^+" for n s t
    using that by (induct n) (auto intro: ranked_path_context[OF _ ctx] ranked_path_subst[OF _ sub])
  have edges: "\<forall>n. (ranked_loop_iterate C sigma n s,ranked_loop_iterate C sigma (Suc n) s) \<in> (ranked_cstep F R)^+"
    using lift[OF path] by (simp add: ranked_loop_iterate_end)
  have "\<not> SN ((ranked_cstep F R)^+)"
    by (rule steps_imp_not_SN[of "\<lambda>n. ranked_loop_iterate C sigma n s" Suc]) (rule edges[rule_format])
  then show ?thesis using SN_imp_SN_trancl by blast
qed

text \<open>A finite positive ranked rewrite path to a contextual substitution
instance is sufficient for ordinary nontermination. This criterion also covers
native argument-descent witnesses after their contexts have been accumulated.\<close>
theorem conditional_ranked_loop_ordinary_NO:
  assumes "(s,C\<langle>s \<cdot> sigma\<rangle>) \<in>
      (ranked_cstep (to_signature A) (to_conditional_rules R))^+"
    "funas_ctxt C \<subseteq> to_signature A"
    "\<forall>x. funas_term (sigma x) \<subseteq> to_signature A"
  shows "\<not> trs_conditional_terminates A R"
  using ranked_context_substitution_loop[OF assms]
    trs_conditional_terminates_iff_ranked by blast
end
