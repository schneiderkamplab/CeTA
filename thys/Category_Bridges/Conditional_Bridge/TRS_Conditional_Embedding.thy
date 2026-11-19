theory TRS_Conditional_Embedding
  imports Category_Properties.TRS_Conditional_Operational_Properties
    Category_Specification_Bridges.TRS_Standard_Equivalence CTRS.Quasi_Decreasingness
begin
text \<open>The existing structural term, substitution and context bijections
are reused. Only ordered conditional-rule lists need an additional translation.\<close>
definition to_conditional_rules :: "('f,'v) conditional_rule set \<Rightarrow> ('f,'v) ctrs" where
  "to_conditional_rules R = (\<lambda>((l,r),cs).
    ((to_term l,to_term r),map (\<lambda>(s,t). (to_term s,to_term t)) cs)) ` R"

fun conditional_goal_holds where
  "conditional_goal_holds R (CRewrite s t) = ((to_term s,to_term t) \<in> cstep R)"
| "conditional_goal_holds R (CReach s t) = ((to_term s,to_term t) \<in> (cstep R)^*)"

lemma conditional_success_embedding:
  assumes "conditional_success A R g"
  shows "conditional_goal_holds (to_conditional_rules R) g"
  using assms
proof (induct rule: conditional_success.induct)
  case ("derive" g gs)
  from "derive.hyps"(1) show ?case
  proof cases
    case (reflexive s)
    then show ?thesis by simp
  next
    case (transitive s u t)
    have first: "(to_term s,to_term u) \<in> cstep (to_conditional_rules R)"
      using "derive" transitive by simp
    have rest: "(to_term u,to_term t) \<in> (cstep (to_conditional_rules R))^*"
      using "derive" transitive by simp
    have "(to_term s,to_term t) \<in> (cstep (to_conditional_rules R))^*"
      by (rule converse_rtrancl_into_rtrancl[OF first rest])
    then show ?thesis by (simp only: transitive(1) conditional_goal_holds.simps)
  next
    case (rule l r cs C sigma)
    have member: "((to_term l,to_term r),map (\<lambda>(s,t). (to_term s,to_term t)) cs)
        \<in> to_conditional_rules R"
      unfolding to_conditional_rules_def
      using imageI[of "((l,r),cs)" R "\<lambda>((l,r),cs). ((to_term l,to_term r),map (\<lambda>(s,t). (to_term s,to_term t)) cs)"] rule by simp
    have conditions: "\<forall>(s,t)\<in>set (map (\<lambda>(s,t). (to_term s,to_term t)) cs).
       (s \<cdot> to_substitution sigma,t \<cdot> to_substitution sigma)
         \<in> (cstep (to_conditional_rules R))^*"
      using "derive" rule by (auto simp: list_all_iff)
    show ?thesis unfolding rule(1) conditional_goal_holds.simps translate_plug translate_subst
      by (rule cstepI[OF member conditions refl refl])
  qed
qed

lemma conditional_step_embedding:
  "conditional_step A R s t \<Longrightarrow>
    (to_term s,to_term t) \<in> cstep (to_conditional_rules R)"
  using conditional_success_embedding[of A R "CRewrite s t"]
  by (simp add: conditional_step_def)

theorem conditional_ordinary_termination_transfer:
  assumes "SN (cstep (to_conditional_rules R))"
  shows "trs_conditional_terminates A R"
proof (rule ccontr)
  assume "\<not> trs_conditional_terminates A R"
  then obtain ts where "\<forall>i. conditional_step A R (ts i) (ts (Suc i))"
    by (auto simp: trs_conditional_nontermination_iff)
  then have "\<forall>i. (to_term (ts i),to_term (ts (Suc i))) \<in> cstep (to_conditional_rules R)"
    using conditional_step_embedding by blast
  then have "\<exists>f. \<forall>i. (f i,f (Suc i)) \<in> cstep (to_conditional_rules R)"
    by (intro exI[of _ "to_term \<circ> ts"]) simp
  with assms show False unfolding SN_defs by blast
qed
end
