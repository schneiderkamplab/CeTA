theory LP_Prolog_Observer_Frontier_Local_Check
 imports LP_Prolog_Observer_Frontier_Ordinary_Check LP_Prolog_Observer_Frontier_Unification_Check LP_Prolog_Observer_Frontier_Is_Check
begin

fun lpp_check_frontier_observer_test where
 "lpp_check_frontier_observer_test frontier_nodes separation_contexts i nd
  ((LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved)
  (LPPFTest yes no yes_facts no_facts) =
   list_all (\<lambda>holds. lpp_check_frontier_observer_target frontier_nodes separation_contexts i
     (if holds then yes else no)) (lpp_var_outcomes f (lpcn_ground nd) a)"
| "lpp_check_frontier_observer_test frontier_nodes separation_contexts i nd ss action = False"

fun lpp_check_frontier_observer_is where
 "lpp_check_frontier_observer_is frontier_nodes separation_contexts
  ((LPCGoals (LPCAtom (Fun (LPCUser f) [a,e])#gs),active)#saved)
  (LPPFIs result_var middle facts) =
   (f=''2:is'' \<and> lpcl_target middle\<in>frontier_nodes \<and>
    lpp_empty_separation_target separation_contexts middle)"
| "lpp_check_frontier_observer_is frontier_nodes separation_contexts ss action = False"

lemma lpp_checked_frontier_test_dispatch:
 fixes SP :: "string lpp_success_clause list"
 assumes program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest={}"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) source_returned arity action"
 and extra: "lpp_check_frontier_observer_test frontier_nodes separation_contexts i (nds!i) (states!i) action"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature
   (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts))
   (lpp_observer_invariant A specs rest) rest returned i"
proof -
 obtain f a gs active saved yes no yes_facts no_facts where
  shape: "states!i=(LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved"
  and action: "action=LPPFTest yes no yes_facts no_facts"
  and targets: "list_all (\<lambda>holds. lpp_check_frontier_observer_target frontier_nodes separation_contexts i
     (if holds then yes else no)) (lpp_var_outcomes f (lpcn_ground (nds!i)) a)"
  using extra by (cases "(frontier_nodes,separation_contexts,i,nds!i,states!i,action)"
    rule: lpp_check_frontier_observer_test.cases) auto
 show ?thesis
  apply (rule lpp_checked_frontier_observer_test_node_contract[OF program clear compatible transfer checked[unfolded action] shape])
  using targets by (auto simp: list_all_iff lpp_check_frontier_observer_target_def)
qed

lemma lpp_checked_frontier_is_dispatch:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest={}"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) source_returned arity action"
 and extra: "lpp_check_frontier_observer_is frontier_nodes separation_contexts (states!i) action"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature
   (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts))
   (lpp_observer_invariant A specs rest) rest returned i"
proof -
 obtain a e gs active saved result_var middle facts where
  shape: "states!i=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
  and action: "action=LPPFIs result_var middle facts"
  and member: "lpcl_target middle\<in>frontier_nodes"
  and empty: "lpp_empty_separation_target separation_contexts middle"
  using extra by (cases "(frontier_nodes,separation_contexts,states!i,action)"
    rule: lpp_check_frontier_observer_is.cases) auto
 have source: "lpp_check_observed_functor_link T facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) a e gs active saved result_var middle"
  using checked by (simp add: shape action lpp_check_functor_source_action_def)
 show ?thesis by (rule lpp_checked_frontier_observer_is_node_contract[OF program clear compatible transfer source member empty])
qed

end
