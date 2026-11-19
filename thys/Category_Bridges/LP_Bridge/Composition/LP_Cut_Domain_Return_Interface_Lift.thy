theory LP_Cut_Domain_Return_Interface_Lift
  imports LP_Cut_Domain_Return_Interface
begin

context cut_runtime_domain
begin

lemma precise_reinterface_forward:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and step: "precise_answer_transition P ss event tt"
  shows "precise_answer_transition P (lpc_reinterface F ss) (map_option F event) (lpc_reinterface F tt)"
  using step
proof (induct rule: precise_answer_transition.induct)
  case (backtrack c a gs m eta es)
  show ?case by (simp only: lpc_reinterface_def list.map case_prod_conv option.map;
    rule precise_answer_transition.backtrack[OF backtrack])
next
  case (unify_fail a b gs eta es)
  show ?case by (simp only: lpc_reinterface_def list.map case_prod_conv option.map;
    rule precise_answer_transition.unify_fail[OF unify_fail])
qed (auto simp: lpc_reinterface_def lpc_reinterface_prune[unfolded lpc_reinterface_def split_def] commute map_map o_def split_def
  intro: precise_answer_transition.intros)

lemma precise_reinterface_path_forward:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and path: "(ss,tt)\<in>(precise_answer_steps P)\<^sup>*"
  shows "(lpc_reinterface F ss,lpc_reinterface F tt)\<in>(precise_answer_steps P)\<^sup>*"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case by simp
next
  case (step tt uu)
  obtain event where event: "precise_answer_transition P tt event uu"
    using step by (auto simp: precise_answer_steps_def)
  have edge: "(lpc_reinterface F tt,lpc_reinterface F uu)\<in>precise_answer_steps P"
    using precise_reinterface_forward[where F=F, OF commute event] by (auto simp: precise_answer_steps_def)
  show ?case using step edge by (blast intro: rtrancl_into_rtrancl)
qed

theorem precise_return_contract_lift_interface:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and contract: "precise_return_contract P (lpc_reinterface F ss) R t ret"
    and bridge: "\<And>eta. (ret (F eta),final eta)\<in>R\<^sup>*"
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
  show "(t,final eta)\<in>R\<^sup>*" by (rule rtrancl_trans[OF returns bridge])
qed

end
end
