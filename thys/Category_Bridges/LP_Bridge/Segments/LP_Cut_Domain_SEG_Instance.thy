theory LP_Cut_Domain_SEG_Instance
 imports LP_Cut_Domain_SEG_Control
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_seg_checked_instance_contract:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_seg_check_instance_boundary e G guards vs observed child H guards' child_vars bindings swaps"
    and program: "lp_cut_source_program P"
    and known: "knowledge (set G) guards eta"
    and child_contract: "precise_return_contract P
      (lpc_return_eval (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta) [(child,map Var child_vars)]) R u ret"
    and entry: "(t,u)\<in>R\<^sup>*"
    and bridge: "\<And>us tail rho.
      (lpc_return_eval eta [(e,map Var vs)],us)\<in>(precise_answer_steps P)\<^sup>* \<Longrightarrow>
      precise_answer_transition P us (Some rho) tail \<Longrightarrow>
      (u,ret (lpc_seg_observe (map (lpc_seg_position_template vs) (map (lp_cut_instance_subst bindings) child_vars)) rho))\<in>R\<^sup>* \<Longrightarrow>
      (ret (lpc_seg_observe (map (lpc_seg_position_template vs) (map (lp_cut_instance_subst bindings) child_vars)) rho),
       final (lpc_seg_observe (map (lpc_seg_position_template vs) observed) rho))\<in>R\<^sup>*"
  shows "precise_return_contract P (lpc_return_eval eta [(e,observed)]) R t final"
proof -
  let ?mu = "lp_cut_instance_subst bindings"
  let ?outputs = "map ?mu child_vars"
  let ?cf = "lpc_seg_observe (map (lpc_seg_position_template vs) ?outputs)"
  let ?pf = "lpc_seg_observe (map (lpc_seg_position_template vs) observed)"
  let ?ss = "lpc_return_eval eta [(e,map Var vs)]"
  have distinct: "distinct vs"
    and out_vars: "\<And>x. x\<in>set ?outputs \<Longrightarrow> vars_term x \<subseteq> set vs"
    and obs_vars: "\<And>x. x\<in>set observed \<Longrightarrow> vars_term x \<subseteq> set vs"
    and annotated: "[(e,?outputs)] = lpc_return_scope_word swaps
      (lpc_return_map (\<lambda>t. t\<cdot>?mu) [(child,map Var child_vars)])"
    using checked by (auto simp: lpc_seg_check_instance_boundary_def Let_def list_all_iff)
  have scoped: "precise_return_contract P
      (lpc_return_scope_word swaps (lpc_return_eval (\<lambda>x. lp_ieval (?mu x) eta) [(child,map Var child_vars)])) R u ret"
    by (rule precise_return_contract_scopes[OF program child_contract])
  have same: "lpc_return_eval eta [(e,?outputs)] =
      lpc_return_scope_word swaps (lpc_return_eval (\<lambda>x. lp_ieval (?mu x) eta) [(child,map Var child_vars)])"
    by (simp only: annotated lpc_return_eval_scopes lpc_return_eval_subst)
  have child: "precise_return_contract P (lpc_reinterface ?cf ?ss) R u ret"
    using scoped same by (simp only: lpc_seg_observe_singleton[OF distinct out_vars])
  have parent: "precise_return_contract P (lpc_reinterface ?pf ?ss) R t final"
    by (rule precise_seg_boundary_contract[where child_observe="?cf" and parent_observe="?pf",
      OF lpc_seg_observe_commutes lpc_seg_observe_commutes child entry bridge])
  show ?thesis using parent by (simp only: lpc_seg_observe_singleton[OF distinct obs_vars])
qed


lemma precise_seg_instance_boundary_knowledge:
  assumes checked: "lpc_seg_check_instance_boundary e G guards vs observed child H guards' child_vars bindings swaps"
    and known: "knowledge (set G) guards eta"
  shows "knowledge (set H) guards' (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta)"
proof -
  have inst: "lp_cut_check_instance [e] G guards [child] H guards' bindings swaps"
    using checked by (simp add: lpc_seg_check_instance_boundary_def Let_def)
  show ?thesis by (rule instance_knowledge[OF inst known])
qed


end
end
