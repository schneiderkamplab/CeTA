theory LP_Prolog_Static_Returns
 imports LP_Prolog_Triple_Captured LP_Cut_SEG_Split_Bridge
begin

lemma lpp_static_domain_answer:
  assumes safe: "lpp_static_state A (map fst ss)"
    and disjoint: "A\<inter>lpp_builtin_signature={}"
    and step: "lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain ss event tt"
  shows "lpc_answer_transition P ss event tt"
proof -
  have inactive: "\<not>lpp_builtin_active lpp_builtin_signature (map fst ss)"
    by (rule lpp_static_no_builtin[OF safe disjoint])
  have good: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_integer_source_domain (map fst ss)"
    by (rule lpp_no_builtin_domain_bad[OF inactive])
  have actual: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin ss event tt"
    using step good by (simp add: lpp_domain_answers_def)
  show ?thesis using actual inactive
    by (cases rule: lpp_answer_transition.cases)
      (auto simp: lpp_builtin_active_def simp del: lpp_integer_source_builtin.simps dest: lpp_integer_source_selected)
qed

lemma lpp_static_actual_return:
  assumes actual: "lpp_actual_return P ss eta"
    and safe: "lpp_static_state A (map fst ss)"
    and program: "lpp_static_program A P"
    and disjoint: "A\<inter>lpp_builtin_signature={}"
  shows "lpc_actual_return P ss eta"
proof -
  obtain us tail where path: "(ss,us)\<in>(lp_answer_steps (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain))\<^sup>*"
    and event: "lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain us (Some eta) tail"
    using actual by (auto simp: lp_actual_answer_def)
  have reached: "(ss,us)\<in>(lpc_answer_steps P)\<^sup>* \<and> lpp_static_state A (map fst us)"
    using path
  proof (induct rule: rtrancl_induct)
    case base show ?case using safe by simp
  next
    case (step ys zs)
    obtain ev where source: "lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain ys ev zs"
      using step.hyps(2) by (auto simp: lp_answer_steps_def)
    have safe': "lpp_static_state A (map fst ys)" using step.hyps(3) by simp
    have local: "lpc_answer_transition P ys ev zs"
      by (rule lpp_static_domain_answer[OF safe' disjoint source])
    have edge: "(ys,zs)\<in>lpc_answer_steps P" using local by (auto simp: lpc_answer_steps_def)
    have target: "lpp_static_state A (map fst zs)"
      by (rule lpp_static_mgu_preserved[OF lpc_answer_transition_erases[OF local] program safe'])
    show ?case using step.hyps(3) edge target by (blast intro: rtrancl_into_rtrancl)
  qed
  have local: "lpc_answer_transition P us (Some eta) tail"
    by (rule lpp_static_domain_answer[OF _ disjoint event]) (use reached in simp)
  show ?thesis using reached local by (auto simp: lpc_actual_return_def)
qed

lemma lpp_static_return_ground_environment:
  assumes checked: "lpc_seg_check_return_ground P pre G vs (Fun LPCTruth (map Var H)) ground_program Fs modes"
    and known: "\<forall>x\<in>set G. lp_seg_ground (eta x)"
    and actual: "lpp_actual_return P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
    and safe: "lpp_static_state A (map fst (lpc_return_eval eta [(LPCGoals pre,map Var vs)]))"
    and program: "lpp_static_program A P"
    and disjoint: "A\<inter>lpp_builtin_signature={}"
    and distinct: "distinct vs" and covered: "set H \<subseteq> set vs"
    and rho: "rho=lpc_return_env (map Var vs) theta"
  shows "\<forall>x\<in>set H. lp_seg_ground (theta x)"
  by (rule lpc_seg_return_ground_environment[OF checked known
    lpp_static_actual_return[OF actual safe program disjoint] distinct covered rho])

end
