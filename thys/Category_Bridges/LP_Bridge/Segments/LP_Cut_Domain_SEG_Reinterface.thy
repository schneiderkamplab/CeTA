theory LP_Cut_Domain_SEG_Reinterface
 imports LP_Cut_Domain_SEG_Interfaces
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_seg_lift_interface_actual:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and contract: "precise_return_contract P (lpc_reinterface F ss) R t ret"
    and bridge: "\<And>us tail eta. (ss,us)\<in>(precise_answer_steps P)\<^sup>* \<Longrightarrow>
      precise_answer_transition P us (Some eta) tail \<Longrightarrow>
      (t,ret (F eta))\<in>R\<^sup>* \<Longrightarrow> (ret (F eta),final eta)\<in>R\<^sup>*"
  shows "precise_return_contract P ss R t final"
proof (unfold precise_return_contract_def, intro conjI allI impI)
  show "SN_on (precise_source P) {map fst ss}"
    using contract by (simp add: precise_return_contract_def)
next
  fix us tail eta
  assume path: "(ss,us)\<in>(precise_answer_steps P)\<^sup>*"
    and event: "precise_answer_transition P us (Some eta) tail"
  have reached: "(lpc_reinterface F ss,lpc_reinterface F us)\<in>(precise_answer_steps P)\<^sup>*"
    by (rule precise_reinterface_path_forward[where F=F, OF commute path])
  have emitted: "precise_answer_transition P (lpc_reinterface F us) (Some (F eta)) (lpc_reinterface F tail)"
    using precise_reinterface_forward[where F=F, OF commute event] by simp
  have returns: "(t,ret (F eta))\<in>R\<^sup>*"
    using contract reached emitted unfolding precise_return_contract_def by blast
  show "(t,final eta)\<in>R\<^sup>*" by (rule rtrancl_trans[OF returns bridge[OF path event returns]])
qed


theorem precise_seg_boundary_contract:
  assumes child_commute: "\<And>eta sigma. child_observe (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (child_observe eta y) sigma)"
    and parent_commute: "\<And>eta sigma. parent_observe (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (parent_observe eta y) sigma)"
    and child: "precise_return_contract P (lpc_reinterface child_observe ss) R u ret"
    and entry: "(t,u)\<in>R\<^sup>*"
    and bridge: "\<And>us tail eta. (ss,us)\<in>(precise_answer_steps P)\<^sup>* \<Longrightarrow>
      precise_answer_transition P us (Some eta) tail \<Longrightarrow>
      (u,ret (child_observe eta))\<in>R\<^sup>* \<Longrightarrow>
      (ret (child_observe eta),final (parent_observe eta))\<in>R\<^sup>*"
  shows "precise_return_contract P (lpc_reinterface parent_observe ss) R t final"
proof -
  have full: "precise_return_contract P ss R u (\<lambda>eta. final (parent_observe eta))"
    by (rule precise_seg_lift_interface_actual[where F=child_observe, OF child_commute child bridge])
  have parent: "precise_return_contract P (lpc_reinterface parent_observe ss) R u final"
    by (rule precise_return_contract_project[where F=parent_observe, OF parent_commute full]) simp
  show ?thesis by (rule precise_return_contract_start[OF entry parent])
qed


end
end
