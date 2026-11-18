theory LP_Prolog_Return_Leaf_Node_Contract
 imports LP_Prolog_Return_Leaf_Coverage LP_Prolog_Separation_Finite_Unification
begin

lemma lpp_leaf_empty_separation_anchored_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (Fun f actuals) gs c m active saved k l A next anchors resolution_bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCClause (LPCAtom (Fun f actuals)#gs) c m,active)#saved)"
 and head: "fst (P!c)=Fun f hs"
 and lengths: "length actuals=length hs"
 and anchored: "lpp_check_anchored_head G actuals hs"
 and ground: "set G \<subseteq> set (lpcn_ground (nds!i)) \<union> lpp_source_context_ground (contexts!i)"
 and coverage: "lpp_check_return_leaf_coverage (map fst specs) active (Fun f actuals) gs"
 and success_target: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow> lpp_empty_separation_target separation_contexts yes"
 and failure_target: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow> lpp_empty_separation_target separation_contexts no"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts (lpp_separation_node_conditions separation_contexts)
   (\<lambda>ss. lpp_finite_execution ss \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ss) returned arity i"
proof (rule lpp_empty_separation_resolution_node_contract[OF compatible transfer checked shape success_target failure_target])
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
 have runtime_ground: "lp_seg_ground (eta x)" if "x\<in>set G" for x
  using ground known lpp_stable_context_ground_sound[OF observed] that
  by (auto simp: lp_cut_knowledge_def)
 have after_finite: "lpp_finite_execution ys"
  using lpp_finite_anchored_resolution_base_step[OF _ _ head lengths anchored runtime_ground] step finite
  by (simp add: shape lpc_return_eval_def)
 have call_finite: "lpp_finite_term (lp_ieval (Fun f actuals) eta)"
  and rest_finite: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
  using finite by (auto simp: shape lpc_return_eval_def lpp_finite_execution_def lpp_finite_goals_def)
 have after_leaf: "lpp_leaf_stack_invariant {u. vars_term u={}} specs ys"
  by (rule lpp_return_anchored_leaf_base_step[OF _ _ coverage anchored head lengths runtime_ground call_finite rest_finite])
    (use step invariant in \<open>auto simp: shape\<close>)
 show "lpp_finite_execution ys \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ys"
  using after_finite after_leaf by simp
qed

ML \<open>
val checked = @{thms lpp_leaf_empty_separation_anchored_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted return leaf node contract" else ();
\<close>
end
