theory LP_Prolog_Forest_Split_Contract
 imports LP_Prolog_Attached_Forest_Answer_Contract LP_Prolog_Functor_Split_Contract
begin

theorem lpp_forest_split_actual_contract:
 fixes vs :: "string list"
 and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and head_shape :: "(string lp_cut_symbol+unit,unit) term"
 and xs :: "(string lp_cut_symbol+unit,unit) term list"
 assumes program: "lp_cut_source_program P"
 and shape: "lpc_check_return_split_shape bindings indices pre rest interface original"
 and arity: "length indices=arity"
 and projection: "lpc_check_return_projection_edge Q vs continuation_returned returned indices"
 and prefix: "lp_answer_contract
   (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta [(LPCGoals pre,interface)]) (lp_ild Q) t prefix_return"
 and initial: "lpp_leaf_stack_invariant A specs (lpc_return_eval eta [(LPCGoals pre,interface)])"
 and preserve: "\<And>us ev ws. lpp_leaf_stack_invariant A specs us \<Longrightarrow>
   (lpc_return_eval eta [(LPCGoals pre,interface)],us)\<in>
    (lp_answer_steps (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain))\<^sup>* \<Longrightarrow>
   lpc_prefix_active us \<Longrightarrow>
   lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
    (lpc_attach_answers (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest) us) ev
    (lpc_attach_answers (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest) ws) \<Longrightarrow>
   lpp_leaf_stack_invariant A specs ws"
 and member: "(slot,lpp_structural_argument_list xs)\<in>set specs"
 and ground: "\<And>u. u\<in>A \<Longrightarrow> vars_term u={}"
 and observed_head: "lpp_runtime_structure head_value head_shape"
 and continuation: "\<And>rho ys. lp_actual_answer
   (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta [(LPCGoals pre,interface)]) rho \<Longrightarrow>
   lpp_runtime_structure (rho slot) (lpp_structural_argument_list ys) \<Longrightarrow>
   ((Inr ys :: (string lp_cut_symbol+unit,unit) term + (string lp_cut_symbol+unit,unit) term list),Inr (head_shape#xs))\<in>lpp_forest_call_order \<Longrightarrow>
   lp_answer_contract
    (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho))
       (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)),rho)]
    (lp_ild Q) (prefix_return rho) (\<lambda>theta. [(continuation_returned,map theta [0..<length vs])])"
 shows "lp_answer_contract
   (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_return_eval eta original) (lp_ild Q) t (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof -
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?gs = "map (lp_cut_map (map_term id (lpc_return_route bindings))) rest"
 let ?ss = "lpc_return_eval eta [(LPCGoals pre,interface)]"
 let ?cont = "\<lambda>rho. [(continuation_returned,map rho [0..<length vs])]"
 have valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ?ss"
  by (simp add: lpc_return_eval_def)
 have separated: "lpc_rest_scopes ?gs \<inter> set (lpc_barrier_ids (map fst ?ss))={}"
  by (simp add: lpc_return_eval_def)
 have composed: "lp_answer_contract ?T (lpc_attach_answers ?gs ?ss) (lp_ild Q) t ?cont"
  apply (rule lpp_attached_forest_answer_contract[where head_value=head_value and head_shape=head_shape and xs=xs and A=A and slot=slot,
    OF program prefix valid separated initial])
  subgoal for us ev ws by (rule preserve) assumption+
  subgoal by (rule member)
  subgoal for u by (rule ground) assumption
  subgoal by (rule observed_head)
  subgoal for rho ys by (rule continuation[of rho ys]; assumption)
  done
 have bridge: "(?cont rho,[(returned,map (lpc_project_interface indices rho) [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
   for rho :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  using lpc_return_projection_edge_sound[OF projection, of rho] arity by auto
 have projected: "lp_answer_contract ?T
   (lpc_reinterface (lpc_project_interface indices) (lpc_attach_answers ?gs ?ss))
   (lp_ild Q) t (\<lambda>rho. [(returned,map rho [0..<arity])])"
  by (rule lpp_domain_contract_project[where F="lpc_project_interface indices",
       OF lpc_project_interface_commutes composed bridge])
 show ?thesis using projected lpc_return_split_shape_sound[OF shape, of eta] by simp
qed

end
