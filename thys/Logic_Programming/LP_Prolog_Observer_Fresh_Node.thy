theory LP_Prolog_Observer_Fresh_Node
 imports LP_Prolog_Observer_Resolution_Node
begin

theorem lpp_checked_observer_fresh_node_contract:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes program: "lp_cut_source_program P"
 and scope_free: "lpc_rest_scopes rest={}"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a gs c m active saved k l A next anchors bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
 and shape: "states!i=((LPCClause (LPCAtom a#gs) c m,active)#saved)"
 and extra: "lpp_check_separation_fresh fuel P (nds!i) separation_contexts i a c k l mode yes no normalized_facts no_separation x y z match_bindings"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature
   (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) (lpp_observer_invariant {v. vars_term v={}} specs rest) rest returned i"
proof -
 have success_transport: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow>
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

  using extra by (auto simp: lpp_check_separation_fresh_def)

 have head_check: "lpp_check_separation_head P (nds!i) (contexts!i) a c (LPPSMatching match_bindings)"
  using extra matching by (simp add: lpp_check_separation_fresh_def)
 show ?thesis
 proof (rule lpp_observer_resolution_node_contract[OF program scope_free compatible transfer checked shape
   head_check success_transport failure_transport _ failed covered])
 fix eta sigma rho
 assume conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and finite_call: "lpp_finite_term (lp_ieval a eta)"
 and mgu: "lpc_mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
    (fst (P!c)) (snd (P!c)) sigma rho"
 have instantiated: "lpp_finite_term (lp_isubst (lp_ieval a eta) sigma)"
   by (rule lpp_matching_head_finite_call_instance[OF matching mgu finite_call])
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

 qed
qed

ML \<open>
val checked = @{thms lpp_checked_observer_fresh_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted observer fresh node" else ();
\<close>
end
