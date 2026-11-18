theory LP_Prolog_Pair_Leaf_Node_Contract
 imports LP_Prolog_Pair_Leaf_Protection
begin
lemma lpp_pair_leaf_base_step:
 assumes step: "lpc_answer_transition P
   (lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),payload)#saved)) event tt"
 and invariant: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   (lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),payload)#saved))"
 and coverage: "lpp_check_ground_relational_leaf_coverage G functors (map fst specs) payload b gs"
 and pair: "lpp_check_separated_pair F separation a b"
 and free: "lpc_free_knowledge (set F) eta"
 and separated: "list_all (lpp_separation_holds eta) separation"
 and protection: "lpp_check_leaf_pair_protection G functors separation a (map fst specs) payload"
 and facts: "list_all (lpp_functor_fact_holds names eta) functors"
 and known: "\<And>x. x\<in>G \<Longrightarrow> lp_seg_ground (eta x)"
 and finite_rhs: "lpp_finite_term (lp_ieval b eta)"
 and finite_rest: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
 shows "lpp_leaf_stack_invariant {u. vars_term u={}} specs tt"
proof (rule lpp_leaf_stack_base_step[OF step invariant])
 show "\<And>a' gs' c m ret es sigma rho.
   lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),payload)#saved) =
    (LPCClause (LPCAtom a'#gs') c m,ret)#es \<Longrightarrow> c<length P \<Longrightarrow>
   lpc_mgu_resolve a' gs' (fst (P!c)) (snd (P!c)) sigma rho \<Longrightarrow>
   lpp_leaf_environment_transport {u. vars_term u={}} specs ret sigma"
  by (simp add: lpc_return_eval_def)
next
 fix a' b' gs' ret es sigma
 assume shape: "lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),payload)#saved) =
   (LPCGoals (LPCUnify a' b'#gs'),ret)#es"
 and mgu: "lpc_mgu_unify a' b' gs' sigma"
 have actual_mgu: "lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
  using mgu shape by (auto simp: lpc_return_eval_def)
 have ret: "ret=lpc_return_env payload eta" using shape by (simp add: lpc_return_eval_def)
 show "lpp_leaf_environment_transport {u. vars_term u={}} specs ret sigma"
  unfolding ret by (rule lpp_checked_pair_leaf_transport[OF pair free separated coverage protection facts known actual_mgu finite_rhs finite_rest])
qed

lemma lpp_leaf_empty_separation_pair_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a b gs active saved k l next mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCGoals (LPCUnify a b#gs),active)#saved)"
 and pair: "lpp_check_separated_pair (Fs!i) (separation_contexts!i) a b"
 and coverage: "lpp_check_ground_relational_leaf_coverage
   (set (lpcn_ground (nds!i)) \<union> lpp_source_context_ground (contexts!i))
   (functor_contexts!i) (map fst specs) active b gs"
 and protection: "lpp_check_leaf_pair_protection
   (set (lpcn_ground (nds!i)) \<union> lpp_source_context_ground (contexts!i))
   (functor_contexts!i) (separation_contexts!i) a (map fst specs) active"
 and success_target: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow> lpp_empty_separation_target separation_contexts yes"
 and failure_target: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow> lpp_empty_separation_target separation_contexts no"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts)
   (\<lambda>ss. lpp_finite_execution ss \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ss) returned arity i"
proof (rule lpp_empty_separation_equality_node_contract[OF compatible transfer checked shape success_target failure_target])
 fix eta ev ys
 assume conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and step: "lpc_answer_transition P (lpc_return_eval eta (states!i)) ev ys"
 and invariant: "lpp_finite_execution (lpc_return_eval eta (states!i)) \<and>
   lpp_leaf_stack_invariant {u. vars_term u={}} specs (lpc_return_eval eta (states!i))"
 have finite: "lpp_finite_execution (lpc_return_eval eta (states!i))" using invariant by simp
 have separated: "list_all (lpp_separation_holds eta) (separation_contexts!i)"
  using conditions by (simp add: lpp_separation_node_conditions_def)
 have after_finite: "lpp_finite_execution ys"
  by (rule lpp_checked_separated_pair_finite_step[OF pair free separated step[unfolded shape] finite[unfolded shape]])
 have known_ground: "lp_seg_ground (eta x)"
  if "x\<in>set (lpcn_ground (nds!i)) \<union> lpp_source_context_ground (contexts!i)" for x
  using known lpp_stable_context_ground_sound[OF observed] that
  by (auto simp: lp_cut_knowledge_def)
 have rhs_finite: "lpp_finite_term (lp_ieval b eta)"
  and rest_finite: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
  using finite by (auto simp: shape lpc_return_eval_def lpp_finite_execution_def lpp_finite_goals_def)
 have after_leaf: "lpp_leaf_stack_invariant {u. vars_term u={}} specs ys"
  by (rule lpp_pair_leaf_base_step[OF _ _ coverage pair free separated protection functors known_ground rhs_finite rest_finite])
    (use step invariant in \<open>auto simp: shape\<close>)
 show "lpp_finite_execution ys \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ys"
  using after_finite after_leaf by simp
qed

ML \<open>
val checked = @{thms lpp_pair_leaf_base_step lpp_leaf_empty_separation_pair_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted pair leaf node contract" else ();
\<close>
end
