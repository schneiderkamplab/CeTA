theory LP_Prolog_Observer_Frontier_Link_Contracts
 imports LP_Prolog_Observer_Frontier_Link
begin

lemma lpp_checked_frontier_observer_context_link:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd source_rows G K eqs F source_context source_functors e"
    and target_member: "lpcl_target e\<in>frontier_nodes"
 and separation_bound: "lpcl_target e<length separation_contexts"
    and separation_check: "lpp_check_separation_transport source_separation (separation_contexts!lpcl_target e)
      (lp_cut_instance_subst (lpcl_bindings e))"
    and separation: "list_all (lpp_separation_holds eta') source_separation"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) K eta'"
    and free: "lpc_free_knowledge (set F) eta'"
    and observed: "lpp_stable_context_holds operation SP source_context eta'"
    and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta' source_rows"
 and invariant: "lpp_leaf_stack_invariant A specs
   (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
 shows "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts))
    (lpc_reinterface (\<lambda>env x. env (Inl x)) (lpc_return_scope_word swaps runtime)) u \<and>
   lpp_leaf_stack_invariant A specs
    (lpc_reinterface (\<lambda>env x. env (Inr x)) (lpc_return_scope_word swaps runtime))"
proof -
 obtain u swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
 and represented_child: "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts))
   (lpc_return_scope_word swaps (lpc_return_eval eta' source_rows)) u"
  using lpp_frontier_separation_functor_link_sound[OF compatible program checked target_member separation_bound
   separation_check separation equations old known free observed functors] by blast
 show ?thesis by (rule exI[of _ u], rule exI[of _ swaps])
  (use strict represented_child invariant in
   \<open>simp add: lpp_observer_reinterface_scopes represented lpp_leaf_stack_scopes\<close>)
qed

lemma lpp_checked_frontier_observer_link_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and program: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_evaluation_functor_link T fs fuel Q nds states contexts Fs functor_contexts nd source_rows G K eqs F source_context source_functors e"
 and target_member: "lpcl_target e\<in>frontier_nodes"
 and separation_bound: "lpcl_target e<length separation_contexts"
 and separation_check: "lpp_check_separation_transport source_separation (separation_contexts!lpcl_target e)
      (lp_cut_instance_subst (lpcl_bindings e))"
 and separation: "list_all (lpp_separation_holds eta') source_separation"
 and equations: "lp_equations eqs eta'"
 and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
 and known: "lp_cut_knowledge (set G) K eta'"
 and free: "lpc_free_knowledge (set F) eta'"
 and observed: "lpp_stable_context_holds operation SP source_context eta'"
 and functors: "list_all (lpp_functor_fact_holds names eta') source_functors"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta' source_rows"
 and invariant: "lpp_leaf_stack_invariant A specs (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
 and lower: "\<And>u swaps.
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts))
    (lpc_reinterface (\<lambda>env x. env (Inl x)) (lpc_return_scope_word swaps runtime)) u \<Longrightarrow>
   lpp_leaf_stack_invariant A specs
    (lpc_reinterface (\<lambda>env x. env (Inr x)) (lpc_return_scope_word swaps runtime)) \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) (lp_ild Q) u returned"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
   (lp_ild Q) [(lpcn_pred nd,map eta (lpcn_vars nd))] returned"
proof -
 obtain u swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
 and child: "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts))
    (lpc_reinterface (\<lambda>env x. env (Inl x)) (lpc_return_scope_word swaps runtime)) u"
 and leaf: "lpp_leaf_stack_invariant A specs
    (lpc_reinterface (\<lambda>env x. env (Inr x)) (lpc_return_scope_word swaps runtime))"
  using lpp_checked_frontier_observer_context_link[OF compatible program checked target_member separation_bound separation_check
    separation equations old known free observed functors represented invariant] by blast
 show ?thesis by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] lower[OF strict child leaf]])
qed

end
