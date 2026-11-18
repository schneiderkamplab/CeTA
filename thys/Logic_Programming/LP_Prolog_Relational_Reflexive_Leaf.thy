theory LP_Prolog_Relational_Reflexive_Leaf
 imports LP_Prolog_Ground_Leaf_Node_Contract LP_Prolog_Separation_Reflexive_Contract
begin

lemma lpp_reflexive_unify_resolution:
 fixes sigma :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_unify (lp_ieval t LPIVar) (lp_ieval t LPIVar) gs sigma"
 shows "lpc_mgu_resolve (lp_ieval t LPIVar) gs t [] sigma sigma"
proof -
 have factor: "\<And>theta :: string \<Rightarrow> ('f,string) lp_iterm. \<exists>delta.
   lp_isubst (lp_isubst (lp_ieval t LPIVar) sigma) delta=lp_isubst (lp_ieval t LPIVar) theta \<and>
   map (lp_cut_map (\<lambda>u. lp_isubst (lp_isubst u sigma) delta)) gs =
   map (lp_cut_map (\<lambda>u. lp_isubst u theta)) gs"
  using mgu unfolding lpc_mgu_unify_def by blast
 show ?thesis unfolding lpc_mgu_resolve_def
 proof (intro conjI allI impI)
  show "lp_isubst (lp_ieval t LPIVar) sigma=lp_ieval t sigma" by (simp add: lp_ieval_subst)
 next
  fix theta nu :: "string \<Rightarrow> ('f,string) lp_iterm"
  assume "lp_isubst (lp_ieval t LPIVar) theta=lp_ieval t nu"
  obtain delta where one: "lp_isubst (lp_isubst (lp_ieval t LPIVar) sigma) delta=lp_isubst (lp_ieval t LPIVar) theta"
   and rest: "map (lp_cut_map (\<lambda>u. lp_isubst (lp_isubst u sigma) delta)) gs =
    map (lp_cut_map (\<lambda>u. lp_isubst u theta)) gs"
   using factor[of theta] by blast
  show "\<exists>delta. lp_isubst (lp_isubst (lp_ieval t LPIVar) sigma) delta=lp_isubst (lp_ieval t LPIVar) theta \<and>
   map (lp_cut_map (\<lambda>u. lp_isubst (lp_isubst u sigma) delta)) gs =
    map (lp_cut_map (\<lambda>u. lp_isubst u theta)) gs \<and>
   map (lp_cut_map (\<lambda>u. lp_isubst (lp_ieval u sigma) delta)) [] =
    map (lp_cut_map (\<lambda>u. lp_ieval u nu)) []"
   by (rule exI[of _ delta]) (use one rest in simp)
 qed
qed

lemma lpp_runtime_reflexive_leaf_images:
 assumes mgu: "lpc_mgu_unify a a gs sigma"
 and finite_call: "lpp_finite_term a"
 and finite_rest: "lpp_finite_goals gs"
 and covered: "V \<subseteq> set2_lp_iterm a \<union>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
 shows "lpp_bounded_images A sigma V"
proof -
 obtain t where represented: "a=lp_ieval t LPIVar"
  using lpp_finite_runtime_template[OF finite_call] by blast
 have resolution: "lpc_mgu_resolve a gs t [] sigma sigma"
  using lpp_reflexive_unify_resolution mgu by (auto simp: represented)
 show ?thesis by (rule lpp_runtime_matching_leaf_images[OF resolution _ finite_call finite_rest covered])
  (simp add: represented)
qed

lemma lpp_relational_reflexive_leaf_transport:
 assumes coverage: "lpp_check_ground_relational_leaf_coverage G facts (map fst specs) payload a gs"
 and facts: "list_all (lpp_functor_fact_holds names eta) facts"
 and ground_known: "\<And>x. x\<in>G \<Longrightarrow> lp_seg_ground (eta x)"
 and mgu: "lpc_mgu_unify (lp_ieval a eta) (lp_ieval a eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
 and finite_call: "lpp_finite_term (lp_ieval a eta)"
 and finite_rest: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
 shows "lpp_leaf_environment_transport {u. vars_term u={}} specs
   (lpc_return_env payload eta) sigma"
proof (unfold lpp_leaf_environment_transport_def, intro ballI impI, clarify)
 fix slot shape
 assume member: "(slot,shape)\<in>set specs"
 and known: "lpp_runtime_leaf_effect {u. vars_term u={}} shape (lpc_return_env payload eta slot)"
 have support: "set2_lp_iterm (lpc_return_env payload eta slot) \<subseteq>
   set2_lp_iterm (lp_ieval a eta) \<union>
    (\<Union>g\<in>set (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs).
      \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
  by (rule lpp_ground_relational_leaf_coverage_sound[OF coverage facts ground_known]) (use member in auto)
 show "lpp_runtime_leaf_effect {u. vars_term u={}} shape
   (lp_isubst (lpc_return_env payload eta slot) sigma)"
  by (rule lpp_runtime_leaf_effect_substitute[OF known
    lpp_runtime_reflexive_leaf_images[OF mgu finite_call finite_rest support]]) simp
qed

lemma lpp_reflexive_leaf_base_step:
 assumes step: "lpc_answer_transition P
   (lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),payload)#saved)) event tt"
 and invariant: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   (lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),payload)#saved))"
 and coverage: "lpp_check_ground_relational_leaf_coverage G facts (map fst specs) payload a gs"
 and facts: "list_all (lpp_functor_fact_holds names eta) facts"
 and known: "\<And>x. x\<in>G \<Longrightarrow> lp_seg_ground (eta x)"
 and equal: "lp_ieval b eta=lp_ieval a eta"
 and finite_call: "lpp_finite_term (lp_ieval a eta)"
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
 have actual_mgu: "lpc_mgu_unify (lp_ieval a eta) (lp_ieval a eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
  using mgu shape equal by (auto simp: lpc_return_eval_def)
 have ret: "ret=lpc_return_env payload eta" using shape by (simp add: lpc_return_eval_def)
 show "lpp_leaf_environment_transport {u. vars_term u={}} specs ret sigma"
  unfolding ret by (rule lpp_relational_reflexive_leaf_transport[OF coverage facts known actual_mgu finite_call finite_rest])
qed

lemma lpp_reflexive_leaf_separation_node_contract:
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

 and coverage: "lpp_check_ground_relational_leaf_coverage
   (set (lpcn_ground (nds!i)) \<union> lpp_source_context_ground (contexts!i))
   (functor_contexts!i) (map fst specs) active a gs"
 and equation: "lpp_check_equation_rewrite (contexts!i) a b"
 and covered: "lpp_check_reflexive_separation k retained gs"
 and incoming: "set retained\<subseteq> set (separation_contexts!i)"
 and failed: "set no_separation\<subseteq> set (separation_contexts!i)"
 and bounds: "2 * k \<le> l"
 shows "lpp_premised_functor_node_contract names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts)
   (\<lambda>ss. lpp_finite_execution ss \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ss) returned arity i"
proof (rule lpp_separation_equality_node_contract[OF compatible transfer checked shape success_transport failure_transport])
 fix eta sigma
 assume conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and invariant: "lpp_finite_execution (lpc_return_eval eta (states!i)) \<and>
   lpp_leaf_stack_invariant {u. vars_term u={}} specs (lpc_return_eval eta (states!i))"
 and mgu: "lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
 have equal: "lp_ieval a eta=lp_ieval b eta"
   by (rule lpp_equation_rewrite_equal[where E="lpp_stable_scalar_evaluation operation" and SP=SP, OF equation])
     (use observed in \<open>simp add: lpp_stable_context_holds_def\<close>)
 have separated: "list_all (lpp_separation_holds eta) retained"
   using incoming conditions by (auto simp: lpp_separation_node_conditions_def list_all_iff)
 have goals: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
   using invariant by (auto simp: shape lpc_return_eval_def lpp_finite_execution_def lpp_finite_goals_def)
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
 and invariant: "lpp_finite_execution (lpc_return_eval eta (states!i)) \<and>
   lpp_leaf_stack_invariant {u. vars_term u={}} specs (lpc_return_eval eta (states!i))"
 have equal: "lp_ieval a eta=lp_ieval b eta"
   by (rule lpp_equation_rewrite_equal[where E="lpp_stable_scalar_evaluation operation" and SP=SP, OF equation])
     (use observed in \<open>simp add: lpp_stable_context_holds_def\<close>)
 have finite: "lpp_finite_execution (lpc_return_eval eta (states!i))" using invariant by simp
 have after_finite: "lpp_finite_execution ys"
   using lpp_finite_reflexive_equality_base_step[OF _ _ equal] step finite
   by (simp add: shape lpc_return_eval_def)
 have known_ground: "lp_seg_ground (eta x)"
  if "x\<in>set (lpcn_ground (nds!i)) \<union> lpp_source_context_ground (contexts!i)" for x
  using known lpp_stable_context_ground_sound[OF observed] that
  by (auto simp: lp_cut_knowledge_def)
 have call_finite: "lpp_finite_term (lp_ieval a eta)"
  and rest_finite: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
  using finite by (auto simp: shape lpc_return_eval_def lpp_finite_execution_def lpp_finite_goals_def)
 have after_leaf: "lpp_leaf_stack_invariant {u. vars_term u={}} specs ys"
  by (rule lpp_reflexive_leaf_base_step[OF _ _ coverage functors known_ground equal[symmetric] call_finite rest_finite])
    (use step invariant in \<open>auto simp: shape\<close>)
 show "lpp_finite_execution ys \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ys"
  using after_finite after_leaf by simp
qed

ML \<open>
val checked = @{thms lpp_reflexive_unify_resolution lpp_runtime_reflexive_leaf_images
 lpp_relational_reflexive_leaf_transport lpp_reflexive_leaf_base_step
 lpp_reflexive_leaf_separation_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted relational reflexive leaf" else ();
\<close>
end
