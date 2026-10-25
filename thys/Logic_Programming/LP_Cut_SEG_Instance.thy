theory LP_Cut_SEG_Instance
  imports LP_Cut_SEG_Observations
begin

definition lpc_seg_check_instance_boundary where
  "lpc_seg_check_instance_boundary e G guards vs observed child H guards' child_vars bindings swaps =
    (let mu=lp_cut_instance_subst bindings;
         outputs=map mu child_vars in
      distinct vs \<and>
      list_all (\<lambda>t. vars_term t \<subseteq> set vs) (observed@outputs) \<and>
      lp_cut_check_instance [e] G guards [child] H guards' bindings swaps \<and>
      [(e,outputs)] = lpc_return_scope_word swaps
        (lpc_return_map (\<lambda>t. t\<cdot>mu) [(child,map Var child_vars)]))"

theorem lpc_seg_checked_instance_contract:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_seg_check_instance_boundary e G guards vs observed child H guards' child_vars bindings swaps"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set G) guards eta"
    and child_contract: "lpc_return_contract P
      (lpc_return_eval (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta) [(child,map Var child_vars)]) R u ret"
    and entry: "(t,u)\<in>R\<^sup>*"
    and bridge: "\<And>us tail rho.
      (lpc_return_eval eta [(e,map Var vs)],us)\<in>(lpc_answer_steps P)\<^sup>* \<Longrightarrow>
      lpc_answer_transition P us (Some rho) tail \<Longrightarrow>
      (u,ret (lpc_seg_observe (map (lpc_seg_position_template vs) (map (lp_cut_instance_subst bindings) child_vars)) rho))\<in>R\<^sup>* \<Longrightarrow>
      (ret (lpc_seg_observe (map (lpc_seg_position_template vs) (map (lp_cut_instance_subst bindings) child_vars)) rho),
       final (lpc_seg_observe (map (lpc_seg_position_template vs) observed) rho))\<in>R\<^sup>*"
  shows "lpc_return_contract P (lpc_return_eval eta [(e,observed)]) R t final"
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
  have scoped: "lpc_return_contract P
      (lpc_return_scope_word swaps (lpc_return_eval (\<lambda>x. lp_ieval (?mu x) eta) [(child,map Var child_vars)])) R u ret"
    by (rule lpc_return_contract_scopes[OF program child_contract])
  have same: "lpc_return_eval eta [(e,?outputs)] =
      lpc_return_scope_word swaps (lpc_return_eval (\<lambda>x. lp_ieval (?mu x) eta) [(child,map Var child_vars)])"
    by (simp only: annotated lpc_return_eval_scopes lpc_return_eval_subst)
  have child: "lpc_return_contract P (lpc_reinterface ?cf ?ss) R u ret"
    using scoped same by (simp only: lpc_seg_observe_singleton[OF distinct out_vars])
  have parent: "lpc_return_contract P (lpc_reinterface ?pf ?ss) R t final"
    by (rule lpc_seg_boundary_contract[where child_observe="?cf" and parent_observe="?pf",
      OF lpc_seg_observe_commutes lpc_seg_observe_commutes child entry bridge])
  show ?thesis using parent by (simp only: lpc_seg_observe_singleton[OF distinct obs_vars])
qed

lemma lpc_seg_instance_boundary_knowledge:
  assumes checked: "lpc_seg_check_instance_boundary e G guards vs observed child H guards' child_vars bindings swaps"
    and known: "lp_cut_knowledge (set G) guards eta"
  shows "lp_cut_knowledge (set H) guards' (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta)"
proof -
  have inst: "lp_cut_check_instance [e] G guards [child] H guards' bindings swaps"
    using checked by (simp add: lpc_seg_check_instance_boundary_def Let_def)
  show ?thesis by (rule lp_cut_checked_instance_knowledge[OF inst known])
qed

end
