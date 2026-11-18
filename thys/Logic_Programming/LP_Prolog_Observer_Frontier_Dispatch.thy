theory LP_Prolog_Observer_Frontier_Dispatch
 imports LP_Prolog_Observer_Frontier_Local_Check
begin

definition lpp_check_frontier_observer_local where
 "lpp_check_frontier_observer_local frontier_nodes P nd source_context separation_contexts i ss action witness =
  (lpp_check_frontier_observer_ordinary frontier_nodes separation_contexts i ss action \<or>
   (lpp_check_frontier_unification_destinations frontier_nodes action \<and>
    lpp_check_separation_unification P nd source_context separation_contexts action witness) \<or>
   lpp_check_frontier_observer_test frontier_nodes separation_contexts i nd ss action \<or>
   lpp_check_frontier_observer_is frontier_nodes separation_contexts ss action)"

theorem lpp_checked_frontier_local_contract:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest={}"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) source_returned arity action"
 and extra: "lpp_check_frontier_observer_local frontier_nodes P (nds!i) (contexts!i) separation_contexts i (states!i) action witness"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature
   (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts))
   (lpp_observer_invariant {v. vars_term v={}} specs rest) rest returned i"
 using extra unfolding lpp_check_frontier_observer_local_def
 apply (elim disjE conjE)
 subgoal by (rule lpp_frontier_observer_ordinary_node_contract[OF program clear compatible transfer checked])
 subgoal by (rule lpp_checked_frontier_observer_unification_node_contract[OF program clear covered compatible transfer checked])
 subgoal by (rule lpp_checked_frontier_test_dispatch[OF program clear compatible transfer checked])
 subgoal by (rule lpp_checked_frontier_is_dispatch[OF program clear compatible transfer checked])
 done

end
