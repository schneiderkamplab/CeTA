theory LP_Prolog_Observer_Module_Link
 imports LP_Prolog_Observer_Rebase
begin

lemma lpp_checked_observer_module_link_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and program: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_evaluation_functor_link T fs fuel Q target_nodes target_states target_contexts target_free target_functors nd source_rows G K eqs F source_context source_functors e"
 and member: "lpcl_target e\<in>target_frontier"
 and bound: "lpcl_target e<length target_separation"
 and transport: "lpp_check_separation_transport source_separation (target_separation!lpcl_target e)
   (lp_cut_instance_subst (lpcl_bindings e))"
 and separation: "list_all (lpp_separation_holds eta') source_separation"
 and equations: "lp_equations eqs eta'"
 and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
 and known: "lp_cut_knowledge (set G) K eta'"
 and free: "lpc_free_knowledge (set F) eta'"
 and observed: "lpp_stable_context_holds operation SP source_context eta'"
 and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
 and representation: "lpc_reinterface (\<lambda>env x. env (Inl x)) (lpp_observer_rebase helper runtime)=lpc_return_eval eta' source_rows"
 and invariant: "lpp_observer_invariant A specs rest runtime"
 and target: "\<And>child u.
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_module_rep names operation SP target_nodes target_states target_contexts target_free target_functors
    (lpp_observer_frontier_conditions target_frontier (lpp_separation_node_conditions target_separation))
    (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<Longrightarrow>
   lpp_observer_invariant A specs rest child \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
   (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))] returned"
proof -
 let ?child = "lpp_observer_rebase helper runtime"
 obtain u swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
 and rep: "lpp_premised_functor_rep names operation SP target_nodes target_states target_contexts target_free target_functors
    (lpp_observer_frontier_conditions target_frontier (lpp_separation_node_conditions target_separation))
    (lpc_return_scope_word swaps (lpc_return_eval eta' source_rows)) u"
  using lpp_frontier_separation_functor_link_sound[OF compatible program checked member bound transport
    separation equations old known free observed functors] by blast
 have module: "lpp_premised_functor_module_rep names operation SP target_nodes target_states target_contexts target_free target_functors
    (lpp_observer_frontier_conditions target_frontier (lpp_separation_node_conditions target_separation))
    (lpc_reinterface (\<lambda>env x. env (Inl x)) ?child) u"
  using rep by (auto simp: lpp_premised_functor_module_rep_def representation)
 have inv: "lpp_observer_invariant A specs rest ?child"
  using invariant by (simp add: lpp_observer_rebase_invariant)
 have result: "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) ?child))
   (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))] returned"
  by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] target[OF strict module inv]])
 show ?thesis using result by (simp add: lpp_observer_rebase_caller)
qed

end
