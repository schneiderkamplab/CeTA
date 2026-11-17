theory LP_Prolog_Finite_Local_Connection
 imports LP_Prolog_Finite_Local_Triple_Observed LP_Prolog_Stable_Guarded_Connection
begin

theorem lpp_finite_local_connection_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_finite_triple_check_connection T fs fuel D Q roots contexts context nd F ss inp out receipt"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and observed: "lpp_stable_context_holds operation SP context eta"
    and free: "lpc_free_knowledge (set F) eta"
    and invariant: "lpc_triple_instance_invariant a inp (lpc_return_eval eta ss)"
    and finite: "lpp_finite_direct_invariant A (lpc_return_eval eta ss)"
    and descent: "(a,lp_atom_eval (lpctr_input (roots!lpctc_target receipt))
      (\<lambda>x. lp_ieval (lp_cut_instance_subst (lpctc_bindings receipt) x) eta))\<in>R"
    and lower: "\<And>us b ret. (a,b)\<in>R \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP contexts roots us b ret \<Longrightarrow> lpp_finite_direct_invariant A us \<Longrightarrow> lpp_stable_triple_answer_contract operation P us Q ret"
  shows "lpp_stable_triple_answer_contract operation P (lpc_return_eval eta ss) Q (lp_atom_eval out)"
proof -
  let ?i = "lpctc_target receipt"
  let ?root = "roots!?i"
  let ?child = "lpctr_node ?root"
  let ?mu = "lp_cut_instance_subst (lpctc_bindings receipt)"
  let ?eta = "\<lambda>x. lp_ieval (?mu x) eta"
  have index: "?i<length roots" "?i<length contexts"
    and transport: "lpp_evaluation_context_transport T fs (lpp_context_add_ground context (lpcn_ground nd)) (contexts!?i) (lpctc_bindings receipt)"
    using checked by (auto simp: lpp_finite_triple_check_connection_def)
  obtain e observed ce where ss: "ss=[(e,observed)]"
    and state: "lpcn_state ?child=[ce]"
    using checked
    by (auto simp: lpp_finite_triple_check_connection_def Let_def split: list.splits prod.splits;
      metis list.exhaust prod.exhaust)
  have inst: "lpc_seg_check_instance_boundary e (lpcn_ground nd) (lpcn_guards nd) (lpcn_vars nd) observed
      ce (lpcn_ground ?child) (lpcn_guards ?child) (lpcn_vars ?child)
      (lpctc_bindings receipt) (lpctc_swaps receipt)"
    and free_check: "lpc_check_link_free fuel [] F (lpctr_free ?root) (lpctc_bindings receipt)"
    and call: "lpc_triple_check_call D [] (lpc_triple_observation_atom observed inp)
      (lp_atom_subst (lpctr_input ?root) ?mu) (lpctc_call receipt) (lpctc_call_bindings receipt)"
    and answer: "lpc_triple_check_instance_answer Q (lpcn_vars nd) observed (lpcn_vars ?child)
      (lpctc_bindings receipt) (lpctr_output ?root) out
      (lpctc_success receipt) (lpctc_success_bindings receipt)"
    using checked by (auto simp: lpp_finite_triple_check_connection_def Let_def ss state)
  have child_known: "lp_cut_knowledge (set (lpcn_ground ?child)) (lpcn_guards ?child) ?eta"
    by (rule lpc_seg_instance_boundary_knowledge[OF inst known])
  have child_free: "lpc_free_knowledge (set (lpctr_free ?root)) ?eta"
    by (rule lpc_checked_link_free_sound[OF free_check _ free]) (simp add: lp_equations_def)
  have enriched: "lpp_stable_context_holds operation SP (lpp_context_add_ground context (lpcn_ground nd)) eta"
    by (rule lpp_stable_add_ground_sound[OF observed])
      (use known in \<open>auto simp: lp_cut_knowledge_def\<close>)
  have child_context: "lpp_stable_context_holds operation SP (contexts!?i) ?eta"
    by (rule lpp_stable_existing_transport_sound[OF compatible transfer transport enriched])
  have rep: "lpp_stable_triple_root_rep operation SP contexts roots (lpc_return_eval ?eta (lpc_triple_root_state ?root))
      (lp_atom_eval (lpctr_input ?root) ?eta) (lp_atom_eval (lpctr_output ?root))"
    unfolding lpp_stable_triple_root_rep_def
    by (rule exI[of _ ?i], rule exI[of _ ?eta]) (use index child_known child_free child_context in simp)
  have annotated: "[(e,map ?mu (lpcn_vars ?child))] = lpc_return_scope_word (lpctc_swaps receipt)
      (lpc_return_map (\<lambda>t. t\<cdot>?mu) [(ce,map Var (lpcn_vars ?child))])"
    using inst by (auto simp: lpc_seg_check_instance_boundary_def Let_def)
  have same: "lpc_return_eval eta [(e,map ?mu (lpcn_vars ?child))] =
      lpc_return_scope_word (lpctc_swaps receipt)
        (lpc_return_eval ?eta [(ce,map Var (lpcn_vars ?child))])"
    by (simp only: annotated lpc_return_eval_scopes lpc_return_eval_subst)
  have finite_parent: "lpp_finite_direct_invariant A
      (lpc_return_eval eta [(e,map ?mu (lpcn_vars ?child))])"
    using finite unfolding ss
    by (simp add: lpp_finite_direct_invariant_def lpp_finite_direct_state_def
      lpc_return_eval_def lpc_return_map_def)
  have finite_child: "lpp_finite_direct_invariant A (lpc_return_eval ?eta (lpc_triple_root_state ?root))"
    using finite_parent unfolding same
    by (simp add: lpp_finite_direct_scopes lpc_triple_root_state_def state)
  have child: "lpp_stable_triple_answer_contract operation P
      (lpc_return_eval ?eta [(ce,map Var (lpcn_vars ?child))]) Q (lp_atom_eval (lpctr_output ?root))"
    using lower[OF descent rep finite_child] by (simp add: lpc_triple_root_state_def state)
  show ?thesis unfolding ss
    by (rule lpp_stable_triple_checked_instance_contract[OF inst program known answer child])
qed

ML \<open>
val checked = [@{thm lpp_finite_local_connection_checked_lower}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable guarded connection dependency" else ();
\<close>
end
