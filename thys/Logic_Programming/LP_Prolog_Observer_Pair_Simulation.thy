theory LP_Prolog_Observer_Pair_Simulation
 imports LP_Prolog_Observer_Equality_Simulation LP_Prolog_Separation_Pair_Control
begin

lemma lpp_separated_pair_node_simulation:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a b gs active saved k l next mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCGoals (LPCUnify a b#gs),active)#saved)"
 and success_transport: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow>
   lpcl_target yes<length separation_contexts \<and>
   lpp_check_separation_transport yes_separation (separation_contexts!lpcl_target yes)
     (lp_cut_instance_subst (lpcl_bindings yes))"
 and failure_transport: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow>
   lpcl_target no<length separation_contexts \<and>
   lpp_check_separation_transport no_separation (separation_contexts!lpcl_target no)
     (lp_cut_instance_subst (lpcl_bindings no))"
 and success_separation: "\<And>eta sigma.
   lpp_separation_node_conditions separation_contexts i eta \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<Longrightarrow>
   lpp_finite_execution (lpc_return_eval eta (states!i)) \<Longrightarrow>
   lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma \<Longrightarrow>
   list_all (lpp_separation_holds (lp_cut_resolution_env k l eta sigma eta)) yes_separation"
 and failure_separation: "\<And>eta :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm. lpp_separation_node_conditions separation_contexts i eta \<Longrightarrow>
   list_all (lpp_separation_holds eta) no_separation"

 and pair: "lpp_check_separated_pair (Fs!i) (separation_contexts!i) a b"
 shows "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution i"
proof (rule lpp_separation_equality_node_simulation[OF compatible transfer checked shape
  success_transport failure_transport success_separation failure_separation])
 fix eta ev ys
 assume conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and step: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 have separated: "list_all (lpp_separation_holds eta) (separation_contexts!i)"
   using conditions by (simp add: lpp_separation_node_conditions_def)
 show "lpp_finite_execution ys"
   by (rule lpp_checked_separated_pair_finite_step[OF pair free separated step[unfolded shape] finite[unfolded shape]])
qed

end
