theory LP_Prolog_Observer_Equality_Check
 imports LP_Prolog_Observer_Equality_Module LP_Prolog_Separation_Acquisition_Check
begin

theorem lpp_checked_separation_reflexive_node_simulation:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a b gs active saved k l next mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCGoals (LPCUnify a b#gs),active)#saved)"
 and extra: "lpp_check_separation_reflexive (nds!i) (contexts!i) separation_contexts i a b gs k l mode yes no retained no_separation"
 shows "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution i"
 apply (rule lpp_reflexive_separation_node_simulation[OF compatible transfer checked shape])
 using extra by (auto simp: lpp_check_separation_reflexive_def)

theorem lpp_checked_separation_pair_node_simulation:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a b gs active saved k l next mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCGoals (LPCUnify a b#gs),active)#saved)"
 and extra: "lpp_check_separation_pair separation_contexts i (Fs!i) a b mode yes no"
 shows "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution i"
 apply (rule lpp_separated_pair_node_simulation[where yes_separation="[]" and no_separation="[]", OF compatible transfer checked shape])
 subgoal using extra by (auto simp: lpp_check_separation_pair_def lpp_empty_separation_branches_def
   lpp_empty_separation_target_def lpp_check_separation_transport_def)
 subgoal using extra by (auto simp: lpp_check_separation_pair_def lpp_empty_separation_branches_def
   lpp_empty_separation_target_def lpp_check_separation_transport_def)
 subgoal by simp
 subgoal by simp
 subgoal using extra by (simp add: lpp_check_separation_pair_def)
 done

end
