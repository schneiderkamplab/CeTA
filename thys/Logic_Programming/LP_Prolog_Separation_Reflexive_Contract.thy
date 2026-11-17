theory LP_Prolog_Separation_Reflexive_Contract
 imports LP_Prolog_Separation_Refresh
begin

lemma lpp_reflexive_separation_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a b gs active saved k l next mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCGoals (LPCUnify a b#gs),active)#saved)"
 and success_transport: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow>
   lpcl_target yes<length separation_contexts \<and>
   lpp_check_separation_transport (map (\<lambda>observation. lpp_separation_subst observation (lp_cut_refresh k (set (lpcn_ground (nds!i))))) retained) (separation_contexts!lpcl_target yes)
     (lp_cut_instance_subst (lpcl_bindings yes))"
 and failure_transport: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow>
   lpcl_target no<length separation_contexts \<and>
   lpp_check_separation_transport no_separation (separation_contexts!lpcl_target no)
     (lp_cut_instance_subst (lpcl_bindings no))"

 and equation: "lpp_check_equation_rewrite (contexts!i) a b"
 and covered: "lpp_check_reflexive_separation k retained gs"
 and incoming: "set retained\<subseteq> set (separation_contexts!i)"
 and failed: "set no_separation\<subseteq> set (separation_contexts!i)"
 and bounds: "2 * k \<le> l"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution returned arity i"
proof (rule lpp_separation_equality_node_contract[OF compatible transfer checked shape success_transport failure_transport])
 fix eta sigma
 assume conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 and mgu: "lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
 have equal: "lp_ieval a eta=lp_ieval b eta"
   by (rule lpp_equation_rewrite_equal[where E="lpp_stable_scalar_evaluation operation" and SP=SP, OF equation])
     (use observed in \<open>simp add: lpp_stable_context_holds_def\<close>)
 have separated: "list_all (lpp_separation_holds eta) retained"
   using incoming conditions by (auto simp: lpp_separation_node_conditions_def list_all_iff)
 have goals: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
   using finite by (auto simp: shape lpc_return_eval_def lpp_finite_execution_def lpp_finite_goals_def)
 have ground: "\<forall>x\<in>set (lpcn_ground (nds!i)). lp_seg_ground (eta x)"
   using known by (simp add: lp_cut_knowledge_def)
 show "list_all (lpp_separation_holds (lp_cut_resolution_env k l eta sigma eta))
   (map (\<lambda>observation. lpp_separation_subst observation (lp_cut_refresh k (set (lpcn_ground (nds!i))))) retained)"
   by (rule lpp_reflexive_separation_refresh[OF covered separated mgu[unfolded equal] goals bounds ground])
next
 fix eta :: "string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm"
 assume "lpp_separation_node_conditions separation_contexts i eta"
 then show "list_all (lpp_separation_holds eta) no_separation"
   using failed by (auto simp: lpp_separation_node_conditions_def list_all_iff)
next
 fix eta ev ys
 assume conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and step: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 have equal: "lp_ieval a eta=lp_ieval b eta"
   by (rule lpp_equation_rewrite_equal[where E="lpp_stable_scalar_evaluation operation" and SP=SP, OF equation])
     (use observed in \<open>simp add: lpp_stable_context_holds_def\<close>)
 show "lpp_finite_execution ys"
   using lpp_finite_reflexive_equality_base_step[OF _ _ equal] step finite
   by (simp add: shape lpc_return_eval_def)
qed

ML \<open>
val checked = @{thms lpp_reflexive_separation_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted reflexive separation node contract" else ();
\<close>
end
