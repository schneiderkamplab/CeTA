theory LP_Prolog_Relational_Matching_Leaf
 imports LP_Prolog_Relational_Return_Leaf
begin

lemma lpp_matching_resolution_leaf_images:
 fixes sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve (lp_ieval call LPIVar)
   (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) h bs sigma rho"
 and matching: "lp_ieval h nu=lp_ieval call LPIVar"
 and covered: "V \<subseteq> vars_term call \<union>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_bounded_images A sigma V"
proof -
 obtain delta where inverse: "\<And>x. x\<in>V \<Longrightarrow> lp_isubst (sigma x) delta=LPIVar x"
  using lpp_matching_context_inverse[OF mgu matching] covered by (auto; blast)
 show ?thesis unfolding lpp_bounded_images_def
  using lpc_isubst_variable_reflect[OF inverse] by blast
qed

lemma lpp_runtime_matching_leaf_images:
 assumes mgu: "lpc_mgu_resolve call gs h bs sigma rho"
 and matching: "lp_ieval h nu=call"
 and finite_call: "lpp_finite_term call"
 and finite_rest: "lpp_finite_goals gs"
 and covered: "V \<subseteq> set2_lp_iterm call \<union>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
 shows "lpp_bounded_images A sigma V"
proof -
 obtain c where call: "call=lp_ieval c LPIVar"
  using lpp_finite_runtime_template[OF finite_call] by blast
 obtain qs where rest: "map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) qs=gs"
  using lpp_finite_goal_templates[OF finite_rest] by blast
 have represented_mgu: "lpc_mgu_resolve (lp_ieval c LPIVar)
   (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) qs) h bs sigma rho"
  using mgu call rest by simp
 have represented_match: "lp_ieval h nu=lp_ieval c LPIVar" using matching call by simp
 have support: "V \<subseteq> vars_term c \<union>
   (\<Union>g\<in>set qs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
  using covered unfolding call rest[symmetric]
  by (simp add: lpp_template_runtime_support lpp_evaluated_goals_runtime_support lpp_finite_goal_map)
 show ?thesis by (rule lpp_matching_resolution_leaf_images[OF represented_mgu represented_match support])
qed

lemma lpp_relational_matching_leaf_transport:
 assumes checked: "lpp_check_relational_leaf_coverage facts (map fst specs) payload call gs"
 and facts: "list_all (lpp_functor_fact_holds names eta) facts"
 and mgu: "lpc_mgu_resolve (lp_ieval call eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
 and matching: "lp_ieval h nu=lp_ieval call eta"
 and finite_call: "lpp_finite_term (lp_ieval call eta)"
 and finite_rest: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
 shows "lpp_leaf_environment_transport {u. vars_term u={}} specs
   (lpc_return_env payload eta) sigma"
proof (unfold lpp_leaf_environment_transport_def, intro ballI impI, clarify)
 fix slot shape
 assume member: "(slot,shape)\<in>set specs"
 and known: "lpp_runtime_leaf_effect {u. vars_term u={}} shape (lpc_return_env payload eta slot)"
 have support: "set2_lp_iterm (lpc_return_env payload eta slot) \<subseteq>
   set2_lp_iterm (lp_ieval call eta) \<union>
    (\<Union>g\<in>set (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs).
      \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
  by (rule lpp_relational_leaf_coverage_sound[OF checked facts]) (use member in auto)
 show "lpp_runtime_leaf_effect {u. vars_term u={}} shape
   (lp_isubst (lpc_return_env payload eta slot) sigma)"
  by (rule lpp_runtime_leaf_effect_substitute[OF known
    lpp_runtime_matching_leaf_images[OF mgu matching finite_call finite_rest support]]) simp
qed


lemma lpp_relational_matching_leaf_base_step:
 assumes step: "lpc_answer_transition P
   (lpc_return_eval eta ((LPCClause (LPCAtom call#gs) c m,payload)#saved)) event tt"
 and invariant: "lpp_leaf_stack_invariant {u. vars_term u={}} specs
   (lpc_return_eval eta ((LPCClause (LPCAtom call#gs) c m,payload)#saved))"
 and coverage: "lpp_check_relational_leaf_coverage facts (map fst specs) payload call gs"
 and facts: "list_all (lpp_functor_fact_holds names eta) facts"
 and matching: "lp_cut_check_match call (fst (P!c)) bindings"
 and finite_call: "lpp_finite_term (lp_ieval call eta)"
 and finite_rest: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
 shows "lpp_leaf_stack_invariant {u. vars_term u={}} specs tt"
proof (rule lpp_leaf_stack_base_step[OF step invariant])
 fix a qs d n ret es sigma rho
 assume shape: "lpc_return_eval eta ((LPCClause (LPCAtom call#gs) c m,payload)#saved) =
   (LPCClause (LPCAtom a#qs) d n,ret)#es"
 and bound: "d<length P"
 and mgu: "lpc_mgu_resolve a qs (fst (P!d)) (snd (P!d)) sigma rho"
 have actual_mgu: "lpc_mgu_resolve (lp_ieval call eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) (fst (P!c)) (snd (P!c)) sigma rho"
  using mgu shape by (auto simp: lpc_return_eval_def)
 have matched: "lp_ieval (fst (P!c)) (\<lambda>x. lp_ieval (lp_cut_match_subst bindings x) eta)=lp_ieval call eta"
  using matching unfolding lp_cut_check_match_def by (simp add: lp_ieval_finite_subst[symmetric])
 have ret: "ret=lpc_return_env payload eta"
  using shape by (simp add: lpc_return_eval_def)
 show "lpp_leaf_environment_transport {u. vars_term u={}} specs ret sigma"
  unfolding ret by (rule lpp_relational_matching_leaf_transport[OF coverage facts actual_mgu matched finite_call finite_rest])
qed (auto simp: lpc_return_eval_def)

lemma lpp_relational_leaf_empty_separation_matching_node_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (a) gs c m active saved k l A next anchors resolution_bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCClause (LPCAtom a#gs) c m,active)#saved)"
 and matching: "lp_cut_check_match a (fst (P!c)) bindings"
 and coverage: "lpp_check_relational_leaf_coverage (functor_contexts!i) (map fst specs) active a gs"
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
 have after_finite: "lpp_finite_execution ys"
  using lpp_finite_matching_resolution_base_step[OF _ _ matching] step finite
  by (simp add: shape lpc_return_eval_def)
 have call_finite: "lpp_finite_term (lp_ieval a eta)"
  and rest_finite: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
  using finite by (auto simp: shape lpc_return_eval_def lpp_finite_execution_def lpp_finite_goals_def)
 have after_leaf: "lpp_leaf_stack_invariant {u. vars_term u={}} specs ys"
  by (rule lpp_relational_matching_leaf_base_step[OF _ _ coverage functors matching call_finite rest_finite])
    (use step invariant in \<open>auto simp: shape\<close>)
 show "lpp_finite_execution ys \<and> lpp_leaf_stack_invariant {u. vars_term u={}} specs ys"
  using after_finite after_leaf by simp
qed

ML \<open>
val checked = @{thms lpp_matching_resolution_leaf_images lpp_runtime_matching_leaf_images
 lpp_relational_matching_leaf_transport lpp_relational_matching_leaf_base_step
 lpp_relational_leaf_empty_separation_matching_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted relational matching leaf" else ();
\<close>
end
