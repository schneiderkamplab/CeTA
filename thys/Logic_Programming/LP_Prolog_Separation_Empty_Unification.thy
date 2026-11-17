theory LP_Prolog_Separation_Empty_Unification
 imports LP_Prolog_Separation_Equality_Contract LP_Prolog_Separation_Resolution_Contract
   LP_Prolog_Separation_Ordinary_Check LP_Prolog_Functor_Spine_Head_Contract
begin

lemma lpp_empty_separation_equality_node_contract:
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
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) J returned arity i"
 apply (rule lpp_separation_equality_node_contract[where yes_separation="[]" and no_separation="[]", OF compatible transfer checked shape])
 subgoal using success_target by (simp add: lpp_empty_separation_target_def lpp_check_separation_transport_def)
 subgoal using failure_target by (simp add: lpp_empty_separation_target_def lpp_check_separation_transport_def)
 subgoal by simp
 subgoal by simp
 subgoal by (rule stable; assumption)
 done

lemma lpp_empty_separation_resolution_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a gs c m active saved k l A next anchors bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCClause (LPCAtom a#gs) c m,active)#saved)"
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
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) J returned arity i"
 apply (rule lpp_separation_resolution_node_contract[where yes_separation="[]" and no_separation="[]", OF compatible transfer checked shape])
 subgoal using success_target by (simp add: lpp_empty_separation_target_def lpp_check_separation_transport_def)
 subgoal using failure_target by (simp add: lpp_empty_separation_target_def lpp_check_separation_transport_def)
 subgoal by simp
 subgoal by simp
 subgoal by (rule stable; assumption)
 done

ML \<open>
val checked = @{thms lpp_empty_separation_equality_node_contract lpp_empty_separation_resolution_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted empty separation unification contracts" else ();
\<close>
end
