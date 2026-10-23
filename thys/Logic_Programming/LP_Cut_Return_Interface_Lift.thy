theory LP_Cut_Return_Interface_Lift
  imports LP_Cut_Return_Interface
begin

lemma lpc_reinterface_forward:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and step: "lpc_answer_transition P ss event tt"
  shows "lpc_answer_transition P (lpc_reinterface F ss) (map_option F event) (lpc_reinterface F tt)"
  using step
  by (cases rule: lpc_answer_transition.cases)
    (auto simp: lpc_reinterface_def lpc_reinterface_prune[unfolded lpc_reinterface_def split_def] commute map_map o_def split_def
      intro: lpc_answer_transition.intros)

lemma lpc_reinterface_path_forward:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and path: "(ss,tt)\<in>(lpc_answer_steps P)\<^sup>*"
  shows "(lpc_reinterface F ss,lpc_reinterface F tt)\<in>(lpc_answer_steps P)\<^sup>*"
  using path
proof (induct rule: rtrancl_induct)
  case base then show ?case by simp
next
  case (step tt uu)
  obtain event where event: "lpc_answer_transition P tt event uu"
    using step by (auto simp: lpc_answer_steps_def)
  have edge: "(lpc_reinterface F tt,lpc_reinterface F uu)\<in>lpc_answer_steps P"
    using lpc_reinterface_forward[where F=F, OF commute event] by (auto simp: lpc_answer_steps_def)
  show ?case using step edge by (blast intro: rtrancl_into_rtrancl)
qed

text \<open>Values outside a finite observed interface must not become new
proof obligations. This converse transfer forgets no execution: it forwards
every actual answer into the independently checked observed contract.\<close>
theorem lpc_return_contract_lift_interface:
  assumes commute: "\<And>eta sigma. F (\<lambda>x. lp_isubst (eta x) sigma) =
      (\<lambda>y. lp_isubst (F eta y) sigma)"
    and contract: "lpc_return_contract P (lpc_reinterface F ss) R t ret"
    and bridge: "\<And>eta. (ret (F eta),final eta)\<in>R\<^sup>*"
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
  show "(t,final eta)\<in>R\<^sup>*" by (rule rtrancl_trans[OF returns bridge])
qed

end
