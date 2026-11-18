theory LP_Prolog_Observer_Frontier_Is_Check
 imports LP_Prolog_Observer_Is_Node
begin

lemma lpp_checked_frontier_observer_is_node_contract:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest={}"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_observed_functor_link T fs fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) a e gs helper_payload helper_saved result_var middle"
 and member: "lpcl_target middle\<in>frontier_nodes"
 and empty: "lpp_empty_separation_target separation_contexts middle"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature
   (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts))
   (lpp_observer_invariant A specs rest) rest returned i"
proof (rule lpp_checked_observer_is_node_contract[OF program clear compatible transfer checked])
 show "lpcl_target middle<length nds"
  using checked by (auto simp: lpp_check_observed_functor_link_def
   lpp_check_evaluation_functor_link_def lpp_check_evaluation_link_def lpc_check_return_table_link_def lpc_check_return_link_def lpc_check_link_def)
next
 show "lpcl_target middle<length states"
  using checked by (auto simp: lpp_check_observed_functor_link_def
   lpp_check_evaluation_functor_link_def lpp_check_evaluation_link_def lpc_check_return_table_link_def lpc_check_return_link_def lpc_check_link_def)
next
 show "lpcl_target middle<length contexts"
  using checked by (auto simp: lpp_check_observed_functor_link_def
   lpp_check_evaluation_functor_link_def lpp_check_evaluation_link_def)
next
 show "lpcl_target middle<length Fs"
  using checked by (auto simp: lpp_check_observed_functor_link_def
   lpp_check_evaluation_functor_link_def lpp_check_evaluation_link_def)
next
 show "lpcl_target middle<length functor_contexts"
  using checked by (auto simp: lpp_check_observed_functor_link_def lpp_check_evaluation_functor_link_def)
next
 show "\<And>rho. lpp_observer_frontier_conditions frontier_nodes
   (lpp_separation_node_conditions separation_contexts) (lpcl_target middle) rho"
  using member empty by (simp add: lpp_observer_frontier_conditions_def
   lpp_separation_node_conditions_def lpp_empty_separation_target_def)
qed

end
