theory LP_Cut_Domain_SEG_Triple_Receipt
 imports LP_Cut_Domain_SEG_Triple_Answers
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_triple_checked_instance_contract:
  fixes P :: "('f,string) lp_cut_program"
  assumes inst: "lpc_seg_check_instance_boundary e G guards vs observed child H guards' child_vars bindings swaps"
    and program: "lp_cut_source_program P"
    and known: "knowledge (set G) guards eta"
    and receipt: "lpc_triple_check_instance_answer Q vs observed child_vars bindings child_out parent_out c sigma"
    and child_contract: "precise_triple_answer_contract P
      (lpc_return_eval (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta)
        [(child,map Var child_vars)]) Q (lp_atom_eval child_out)"
  shows "precise_triple_answer_contract P (lpc_return_eval eta [(e,observed)]) Q (lp_atom_eval parent_out)"
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
    using inst by (auto simp: lpc_seg_check_instance_boundary_def Let_def list_all_iff)
  have scoped: "precise_triple_answer_contract P
    (lpc_return_scope_word swaps (lpc_return_eval (\<lambda>x. lp_ieval (?mu x) eta)
      [(child,map Var child_vars)])) Q (lp_atom_eval child_out)"
    unfolding precise_triple_answer_contract_return_contract
    by (rule precise_return_contract_scopes[OF program])
      (use child_contract in \<open>simp only: precise_triple_answer_contract_return_contract\<close>)
  have same: "lpc_return_eval eta [(e,?outputs)] =
    lpc_return_scope_word swaps (lpc_return_eval (\<lambda>x. lp_ieval (?mu x) eta)
      [(child,map Var child_vars)])"
    by (simp only: annotated lpc_return_eval_scopes lpc_return_eval_subst)
  have child': "precise_triple_answer_contract P (lpc_reinterface ?cf ?ss) Q (lp_atom_eval child_out)"
    using scoped same by (simp only: lpc_seg_observe_singleton[OF distinct out_vars])
  have parent: "precise_triple_answer_contract P (lpc_reinterface ?pf ?ss) Q (lp_atom_eval parent_out)"
  proof (rule precise_triple_answer_boundary[OF lpc_seg_observe_commutes lpc_seg_observe_commutes child'])
    fix rho assume child_model: "lp_answer_model Q (lp_atom_eval child_out (?cf rho))"
    show "lp_answer_model Q (lp_atom_eval parent_out (?pf rho))"
      by (rule lpc_triple_checked_instance_answer[OF receipt child_model])
  qed
  show ?thesis using parent by (simp only: lpc_seg_observe_singleton[OF distinct obs_vars])
qed


end
end
