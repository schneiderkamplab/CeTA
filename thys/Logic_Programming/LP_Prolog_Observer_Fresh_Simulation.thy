theory LP_Prolog_Observer_Fresh_Simulation
 imports LP_Prolog_Observer_Resolution_Simulation
begin

lemma lpp_normalized_fresh_matching_separation_node_simulation:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a gs c m active saved k l A next anchors bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCClause (LPCAtom a#gs) c m,active)#saved)"
 and success_transport: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow>
   lpcl_target yes<length separation_contexts \<and>
   lpp_check_separation_transport normalized_facts (separation_contexts!lpcl_target yes)
     (lp_cut_instance_subst (lpcl_bindings yes))"
 and failure_transport: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow>
   lpcl_target no<length separation_contexts \<and>
   lpp_check_separation_transport no_separation (separation_contexts!lpcl_target no)
     (lp_cut_instance_subst (lpcl_bindings no))"

 and normalization: "lpp_check_separation_normalize fuel
   (lp_cut_resolution_equations k l (lpcn_ground (nds!i)) a (fst (P!c)))
   (map (\<lambda>observation. lpp_separation_subst observation (\<lambda>v. Var (lp_prefix l v)))
     [LPPSeparate (Var x) (Var y),LPPSeparate (Var x) (Var z)]) normalized_facts"
 and bounds: "2 * k \<le> l"
 and short: "\<forall>v\<in>vars_term a. length v<k"
 and matching: "lp_cut_check_match a (fst (P!c)) match_bindings"
 and fresh_clause: "lpp_check_fresh_univ_clause (fst (P!c)) (snd (P!c)) x y z"
 and failed: "set no_separation\<subseteq> set (separation_contexts!i)"
 shows "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution i"
proof (rule lpp_separation_resolution_node_simulation[OF compatible transfer checked shape success_transport failure_transport])
 fix eta sigma rho
 assume conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 and mgu: "lpc_mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
    (fst (P!c)) (snd (P!c)) sigma rho"
 have call_finite: "lpp_finite_term (lp_ieval a eta)"
   using finite by (auto simp: shape lpc_return_eval_def lpp_finite_execution_def lpp_finite_goals_def)
 have instantiated: "lpp_finite_term (lp_isubst (lp_ieval a eta) sigma)"
   by (rule lpp_matching_head_finite_call_instance[OF matching mgu call_finite])
 have acquired: "list_all (lpp_separation_holds (lp_cut_resolution_env k l eta sigma rho))
   (map (\<lambda>observation. lpp_separation_subst observation (\<lambda>v. Var (lp_prefix l v)))
     [LPPSeparate (Var x) (Var y),LPPSeparate (Var x) (Var z)])"
   by (rule lpp_fresh_univ_acquires_clause_separation[OF fresh_clause mgu instantiated])
 have ground: "\<forall>v\<in>set (lpcn_ground (nds!i)). lp_seg_ground (eta v)"
   using known by (simp add: lp_cut_knowledge_def)
 have equality: "lp_isubst (lp_ieval a eta) sigma=lp_ieval (fst (P!c)) rho"
   using mgu by (simp add: lpc_mgu_resolve_def)
 have initialized: "lp_equations (lp_cut_resolution_equations k l (lpcn_ground (nds!i)) a (fst (P!c)))
   (lp_cut_resolution_env k l eta sigma rho)"
   using equality lp_cut_resolution_active[OF short bounds ground]
   by (simp add: lp_equations_def lp_cut_resolution_equations_def lp_cut_resolution_clause)
 show "list_all (lpp_separation_holds (lp_cut_resolution_env k l eta sigma rho)) normalized_facts"
   by (rule lpp_check_separation_normalize_sound[OF normalization initialized acquired])

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
 show "lpp_finite_execution ys"
   by (rule lpp_finite_matching_resolution_base_step[OF _ _ matching])
     (use step finite in \<open>simp_all add: shape lpc_return_eval_def\<close>)
qed

theorem lpp_checked_separation_fresh_node_simulation:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a gs c m active saved k l A next anchors bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCClause (LPCAtom a#gs) c m,active)#saved)"
 and extra: "lpp_check_separation_fresh fuel P (nds!i) separation_contexts i a c k l mode yes no normalized_facts no_separation x y z match_bindings"
 shows "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution i"
 apply (rule lpp_normalized_fresh_matching_separation_node_simulation[OF compatible transfer checked shape])
 using extra by (auto simp: lpp_check_separation_fresh_def)

ML \<open>
val checked = @{thms lpp_separation_resolution_node_simulation lpp_normalized_fresh_matching_separation_node_simulation lpp_checked_separation_fresh_node_simulation};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked)) then error "Untrusted fresh resolution simulation" else ();
\<close>
end
