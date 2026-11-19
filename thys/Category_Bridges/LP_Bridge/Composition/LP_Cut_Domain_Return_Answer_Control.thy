theory LP_Cut_Domain_Return_Answer_Control
 imports LP_Cut_Domain_Return_Preserved_Ground
begin

context cut_runtime_domain
begin

theorem precise_control_answers_preserved:
  assumes program: "lpc_control_program P Q F"
    and step: "precise_answer_transition P ss event tt"
    and known: "list_all (lpc_control_answer_frame Q F origin \<eta>) ss"
  shows "list_all (lpc_control_answer_frame Q F origin \<eta>) tt"
  using step known
proof (cases rule: precise_answer_transition.cases)
  case (truth gs \<rho> es)
  have old: "lpc_control_answer_frame Q F origin \<eta> (LPCGoals (LPCTrue#gs),\<rho>)"
    using known truth by simp
  have continued: "lpc_control_answer_frame Q F origin \<eta> (LPCGoals gs,\<rho>)"
    by (rule lpc_control_answer_drop[OF program old]) simp
  show ?thesis using continued known truth by simp
next
  case (cut m gs \<rho> es)
  have old: "lpc_control_answer_frame Q F origin \<eta> (LPCGoals (LPCCut m#gs),\<rho>)"
    using known cut by simp
  have continued: "lpc_control_answer_frame Q F origin \<eta> (LPCGoals gs,\<rho>)"
    by (rule lpc_control_answer_drop[OF program old]) simp
  show ?thesis using continued known cut lpc_answer_prune_subset[of m es]
    by (auto simp: list_all_iff)
next
  case (resolve c a gs \<sigma> \<rho> m \<nu> es)
  obtain f ts where a: "a=LPIFun (LPCUser f) ts" and f: "f\<in>F"
    and tail: "list_all (lpc_control_igoal F) gs"
    and before: "((origin,\<eta>),((LPCUser f,ts)#map lpc_control_iatom gs,\<nu>))\<in>(lp_seg_answer_step Q)\<^sup>*"
    using known resolve by (auto simp: lpc_control_igoal_iff)
  have eq: "lp_isubst (LPIFun (LPCUser f) ts) \<sigma> = lp_ieval (fst (P!c)) \<rho>"
    using resolve a by (simp add: mgu_resolve_def)
  have c: "c<length P" using resolve by simp
  note domain = lpc_control_resolution(1)[OF program f tail c eq, of m]
  note ast = lpc_control_answer_resolution[OF program f tail c eq, of \<nu> m]
  note path = rtrancl_into_rtrancl[OF before ast]
  show ?thesis using known resolve domain path by simp
qed (auto simp: list_all_iff lpc_control_igoal_iff)

lemma precise_control_answer_trace_invariant:
  assumes program: "lpc_control_program P Q F"
    and path: "(ss,tt)\<in>(precise_answer_steps P)\<^sup>*"
    and known: "list_all (lpc_control_answer_frame Q F origin \<eta>) ss"
  shows "list_all (lpc_control_answer_frame Q F origin \<eta>) tt"
  using path known
proof (induct rule: rtrancl_induct)
  case base then show ?case .
next
  case (step ys zs)
  obtain event where st: "precise_answer_transition P ys event zs"
    using step.hyps(2) by (auto simp: precise_answer_steps_def)
  show ?case by (rule precise_control_answers_preserved[OF program st step.hyps(3)[OF step.prems]])
qed

theorem precise_control_successful_answer:
  assumes program: "lpc_control_program P Q F"
    and domain: "list_all (lpc_control_igoal F) gs"
    and path: "([(LPCGoals gs,\<eta>)],ss)\<in>(precise_answer_steps P)\<^sup>*"
    and event: "precise_answer_transition P ss (Some \<rho>) tt"
  shows "((map lpc_control_iatom gs,\<eta>),([],\<rho>))\<in>(lp_seg_answer_step Q)\<^sup>*"
proof -
  have origin: "list_all (lpc_control_answer_frame Q F (map lpc_control_iatom gs) \<eta>)
    [(LPCGoals gs,\<eta>)]" using domain by simp
  note known = precise_control_answer_trace_invariant[OF program path origin]
  have shape: "ss=(LPCGoals [],\<rho>)#tt" by (rule precise_answer_event_is_success[OF event])
  show ?thesis using known by (simp add: shape)
qed

corollary precise_control_answer_contract_transfer:
  assumes program: "lpc_control_program P Q F"
    and domain: "list_all (lpc_control_igoal F) gs"
    and contract: "\<And>\<rho>. ((map lpc_control_iatom gs,\<eta>),([],\<rho>))\<in>(lp_seg_answer_step Q)\<^sup>* \<Longrightarrow> C \<rho>"
    and path: "([(LPCGoals gs,\<eta>)],ss)\<in>(precise_answer_steps P)\<^sup>*"
    and event: "precise_answer_transition P ss (Some \<rho>) tt"
  shows "C \<rho>"
  by (rule contract[OF precise_control_successful_answer[OF program domain path event]])

corollary precise_control_answers_keep_ground_inputs:
  assumes program: "lpc_control_program P Q F"
    and domain: "list_all (lpc_control_igoal F) gs"
    and path: "([(LPCGoals gs,\<eta>)],ss)\<in>(precise_answer_steps P)\<^sup>*"
    and event: "precise_answer_transition P ss (Some \<rho>) tt"
    and ground: "lp_seg_ground (\<eta> x)"
  shows "\<rho> x = \<eta> x"
  by (rule lp_seg_answer_steps_preserve_ground[OF
    precise_control_successful_answer[OF program domain path event] ground])


end
end
