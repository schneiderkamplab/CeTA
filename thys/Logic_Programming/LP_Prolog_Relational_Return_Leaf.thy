theory LP_Prolog_Relational_Return_Leaf
 imports LP_Prolog_Functor_Leaf_Support
begin

definition lpp_check_relational_leaf_coverage where
 "lpp_check_relational_leaf_coverage facts slots payload call gs =
  (\<forall>slot\<in>set slots. slot < length payload \<and>
    vars_term (payload!slot) \<subseteq> lpp_functor_support_closure facts
     (vars_term call \<union> (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)))"

lemma lpp_relational_leaf_coverage_sound:
 assumes checked: "lpp_check_relational_leaf_coverage facts slots payload call gs"
 and facts: "list_all (lpp_functor_fact_holds names eta) facts"
 and member: "slot\<in>set slots"
 shows "set2_lp_iterm (lpc_return_env payload eta slot) \<subseteq>
   set2_lp_iterm (lp_ieval call eta) \<union>
    (\<Union>g\<in>set (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs).
      \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
proof -
 let ?V = "vars_term call \<union> (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 let ?S = "set2_lp_iterm (lp_ieval call eta) \<union>
    (\<Union>g\<in>set (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs).
      \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
 have initial: "set2_lp_iterm (eta x) \<subseteq> ?S" if "x\<in>?V" for x
  using that by (auto simp: lpp_evaluation_runtime_support lpp_finite_goal_map)
 have covered: "set2_lp_iterm (eta x) \<subseteq> ?S"
  if "x\<in>lpp_functor_support_closure facts ?V" for x
  by (rule lpp_functor_support_closure_sound[OF facts initial that])
 show ?thesis using checked member covered
  by (auto simp: lpp_check_relational_leaf_coverage_def lpc_return_env_def lpp_evaluation_runtime_support; blast)
qed

lemma lpp_relational_ground_head_leaf_transport:
 assumes checked: "lpp_check_relational_leaf_coverage facts (map fst specs) payload call gs"
 and facts: "list_all (lpp_functor_fact_holds names eta) facts"
 and mgu: "lpc_mgu_resolve (lp_ieval call eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
 and finite_call: "lpp_finite_term (lp_ieval call eta)"
 and finite_rest: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
 and ground_head: "lp_seg_ground (lp_ieval h rho)"
 shows "lpp_leaf_environment_transport {u. vars_term u={}} specs
   (lpc_return_env payload eta) sigma"
 by (rule lpp_runtime_ground_head_leaf_transport[OF mgu finite_call finite_rest
   lpp_ground_finite_term[OF ground_head] ground_head])
   (use lpp_relational_leaf_coverage_sound[OF checked facts] in fastforce)

lemma lpp_relational_anchored_head_leaf_transport:
 assumes coverage: "lpp_check_relational_leaf_coverage facts (map fst specs) payload (Fun f actuals) gs"
 and facts: "list_all (lpp_functor_fact_holds names eta) facts"
 and checked: "lpp_check_anchored_head G actuals hs"
 and lengths: "length actuals=length hs"
 and known: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
 and mgu: "lpc_mgu_resolve (lp_ieval (Fun f actuals) eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) (Fun f hs) bs sigma rho"
 and finite_call: "lpp_finite_term (lp_ieval (Fun f actuals) eta)"
 and finite_rest: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
 shows "lpp_leaf_environment_transport {u. vars_term u={}} specs
   (lpc_return_env payload eta) sigma"
proof -
 have equation: "map (\<lambda>t. lp_isubst (lp_ieval t eta) sigma) actuals =
   map (\<lambda>t. lp_ieval t rho) hs"
  using mgu by (simp add: lpc_mgu_resolve_def map_map o_def)
 have ground: "lp_seg_ground (lp_ieval (Fun f hs) rho)"
  by (rule lpp_checked_anchored_head_ground[OF checked lengths known equation])
 show ?thesis by (rule lpp_relational_ground_head_leaf_transport[OF coverage facts mgu finite_call finite_rest ground])
qed

lemma lpp_relational_anchored_leaf_base_step:
 assumes step: "lpc_answer_transition P
   (lpc_return_eval eta ((LPCClause (LPCAtom (Fun f actuals)#gs) c m,payload)#saved)) event tt"
 and invariant: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   (lpc_return_eval eta ((LPCClause (LPCAtom (Fun f actuals)#gs) c m,payload)#saved))"
 and coverage: "lpp_check_relational_leaf_coverage facts (map fst specs) payload (Fun f actuals) gs"
 and facts: "list_all (lpp_functor_fact_holds names eta) facts"
 and checked: "lpp_check_anchored_head G actuals hs"
 and head: "fst (P!c)=Fun f hs"
 and lengths: "length actuals=length hs"
 and known: "\<And>x. x\<in>set G \<Longrightarrow> lp_seg_ground (eta x)"
 and finite_call: "lpp_finite_term (lp_ieval (Fun f actuals) eta)"
 and finite_rest: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
 shows "lpp_leaf_stack_invariant {u. vars_term u={}} specs tt"
proof (rule lpp_leaf_stack_base_step[OF step invariant])
 fix a qs d n ret es sigma rho
 assume shape: "lpc_return_eval eta ((LPCClause (LPCAtom (Fun f actuals)#gs) c m,payload)#saved) =
   (LPCClause (LPCAtom a#qs) d n,ret)#es"
 and bound: "d<length P"
 and mgu: "lpc_mgu_resolve a qs (fst (P!d)) (snd (P!d)) sigma rho"
 have actual_mgu: "lpc_mgu_resolve (lp_ieval (Fun f actuals) eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) (Fun f hs) (snd (P!c)) sigma rho"
  using mgu shape head by (auto simp: lpc_return_eval_def)
 have ret: "ret=lpc_return_env payload eta"
  using shape by (simp add: lpc_return_eval_def)
 show "lpp_leaf_environment_transport {u. vars_term u={}} specs ret sigma"
  unfolding ret by (rule lpp_relational_anchored_head_leaf_transport[OF coverage facts checked lengths known actual_mgu finite_call finite_rest])
qed (auto simp: lpc_return_eval_def)

lemma lpp_relational_leaf_empty_separation_anchored_node_contract:
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
 and coverage: "lpp_check_relational_leaf_coverage (functor_contexts!i) (map fst specs) active (Fun f actuals) gs"
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
  by (rule lpp_relational_anchored_leaf_base_step[OF _ _ coverage functors anchored head lengths runtime_ground call_finite rest_finite])
    (use step invariant in \<open>auto simp: shape\<close>)
 show "lpp_finite_execution ys \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ys"
  using after_finite after_leaf by simp
qed

ML \<open>
val checked = @{thms lpp_relational_leaf_coverage_sound lpp_relational_ground_head_leaf_transport
 lpp_relational_anchored_head_leaf_transport lpp_relational_anchored_leaf_base_step
 lpp_relational_leaf_empty_separation_anchored_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted relational return leaf contracts" else ();
\<close>
end
