theory LP_Prolog_Observer_Ground_Equality_Simulation
 imports LP_Prolog_Observer_Equality_Check
begin

lemma lpp_empty_separation_equality_node_simulation:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a b gs active saved k l next mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCGoals (LPCUnify a b#gs),active)#saved)"
 and success_target: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow> lpp_empty_separation_target separation_contexts yes"
 and failure_target: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow> lpp_empty_separation_target separation_contexts no"
 and stable: "\<And>eta ev ys.
   lpp_separation_node_conditions separation_contexts i eta \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<Longrightarrow>
   lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys \<Longrightarrow>
   J (lpc_return_eval eta (states!i)) \<Longrightarrow> J ys"
 shows "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) J i"
 apply (rule lpp_separation_equality_node_simulation[where yes_separation="[]" and no_separation="[]", OF compatible transfer checked shape])
 subgoal using success_target by (simp add: lpp_empty_separation_target_def lpp_check_separation_transport_def)
 subgoal using failure_target by (simp add: lpp_empty_separation_target_def lpp_check_separation_transport_def)
 subgoal by simp
 subgoal by simp
 subgoal by (rule stable; assumption)
 done

lemma lpp_finite_empty_separation_ground_equality_node_simulation:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a b gs active saved k l next mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCGoals (LPCUnify a b#gs),active)#saved)"
 and ground: "vars_term b \<subseteq> set (lpcn_ground (nds!i)) \<union> lpp_source_context_ground (contexts!i)"
 and success_target: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow> lpp_empty_separation_target separation_contexts yes"
 and failure_target: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow> lpp_empty_separation_target separation_contexts no"
 shows "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts)
   lpp_finite_execution i"
proof (rule lpp_empty_separation_equality_node_simulation[OF compatible transfer checked shape success_target failure_target])
 fix eta ev ys
 assume conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and step: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 have runtime_ground: "lp_seg_ground (lp_ieval b eta)"
  using ground known lpp_stable_context_ground_sound[OF observed]
  by (auto simp: lp_seg_ground_eval lp_cut_knowledge_def)
 show "lpp_finite_execution ys"
  using lpp_finite_ground_equality_base_step[OF _ _ runtime_ground] step finite
  by (simp add: shape lpc_return_eval_def)
qed

end
