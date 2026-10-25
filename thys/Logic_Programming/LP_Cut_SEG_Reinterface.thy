theory LP_Cut_SEG_Reinterface
  imports LP_Cut_SEG_Interfaces
begin

text \<open>At a connection boundary the local table observes all live and
answer-only variables, while the residual order observes only proven-ground
positions. A forward constructor observation suffices even when the matching
substitution is not invertible. The return rule is checked on actual answers,
not on arbitrary impossible environments.\<close>

theorem lpc_seg_lift_interface_actual:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and contract: "lpc_return_contract P (lpc_reinterface F ss) R t ret"
    and bridge: "\<And>us tail eta. (ss,us)\<in>(lpc_answer_steps P)\<^sup>* \<Longrightarrow>
      lpc_answer_transition P us (Some eta) tail \<Longrightarrow>
      (t,ret (F eta))\<in>R\<^sup>* \<Longrightarrow> (ret (F eta),final eta)\<in>R\<^sup>*"
  shows "lpc_return_contract P ss R t final"
proof (unfold lpc_return_contract_def, intro conjI allI impI)
  show "SN_on (lp_cut_mgu_source P) {map fst ss}"
    using contract by (simp add: lpc_return_contract_def)
next
  fix us tail eta
  assume path: "(ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
    and event: "lpc_answer_transition P us (Some eta) tail"
  have reached: "(lpc_reinterface F ss,lpc_reinterface F us)\<in>(lpc_answer_steps P)\<^sup>*"
    by (rule lpc_reinterface_path_forward[where F=F, OF commute path])
  have emitted: "lpc_answer_transition P (lpc_reinterface F us) (Some (F eta)) (lpc_reinterface F tail)"
    using lpc_reinterface_forward[where F=F, OF commute event] by simp
  have returns: "(t,ret (F eta))\<in>R\<^sup>*"
    using contract reached emitted unfolding lpc_return_contract_def by blast
  show "(t,final eta)\<in>R\<^sup>*" by (rule rtrancl_trans[OF returns bridge[OF path event returns]])
qed

theorem lpc_seg_boundary_contract:
  assumes child_commute: "\<And>eta sigma. child_observe (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (child_observe eta y) sigma)"
    and parent_commute: "\<And>eta sigma. parent_observe (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (parent_observe eta y) sigma)"
    and child: "lpc_return_contract P (lpc_reinterface child_observe ss) R u ret"
    and entry: "(t,u)\<in>R\<^sup>*"
    and bridge: "\<And>us tail eta. (ss,us)\<in>(lpc_answer_steps P)\<^sup>* \<Longrightarrow>
      lpc_answer_transition P us (Some eta) tail \<Longrightarrow>
      (u,ret (child_observe eta))\<in>R\<^sup>* \<Longrightarrow>
      (ret (child_observe eta),final (parent_observe eta))\<in>R\<^sup>*"
  shows "lpc_return_contract P (lpc_reinterface parent_observe ss) R t final"
proof -
  have full: "lpc_return_contract P ss R u (\<lambda>eta. final (parent_observe eta))"
    by (rule lpc_seg_lift_interface_actual[where F=child_observe, OF child_commute child bridge])
  have parent: "lpc_return_contract P (lpc_reinterface parent_observe ss) R u final"
    by (rule lpc_return_contract_project[where F=parent_observe, OF parent_commute full]) simp
  show ?thesis by (rule lpc_return_contract_start[OF entry parent])
qed

end
