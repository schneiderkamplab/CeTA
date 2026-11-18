theory LP_Prolog_Observer_Frontier_Fresh_Check
 imports LP_Prolog_Observer_Frontier_Fresh_Node
begin

lemma lpp_checked_frontier_observer_fresh_univ_node_contract:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and program: "lp_cut_source_program P"
 and equality_coverage: "\<And>j (nu :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). j<length nds \<Longrightarrow>
   lpp_observer_equality_frame (lpc_return_eval nu (states!j)) \<Longrightarrow>
   lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) lpp_finite_execution j"
 and univ_coverage: "\<And>i (eta :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). i<length nds \<Longrightarrow>
   lpp_observer_univ_frame (lpc_return_eval eta (states!i)) \<Longrightarrow>
   \<exists>value_var name_var args_var middle facts pair_symbol output_name output_args.
    lpp_check_functor_source_action T fuel P Q nds states contexts Fs functor_contexts
     (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) source_returned source_arity
     (LPPFUniv value_var name_var args_var middle facts) \<and>
    lpp_check_separation_univ separation_contexts i (states!i) name_var args_var middle pair_symbol output_name output_args"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a gs c m helper_payload helper_saved k l A next anchors bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
 and source_shape: "states!i=((LPCClause (LPCAtom a#gs) c m,helper_payload)#helper_saved)"
 and extra: "lpp_check_separation_fresh fuel P (nds!i) separation_contexts i a c k l mode yes no normalized_facts no_separation x y z match_bindings"
 and clear: "lpc_rest_scopes rest={}"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and frontier_shapes: "lpp_check_observer_frontier_shapes frontier_nodes states"
 and exit_coverage: "\<And>j (nu :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). j<length nds \<Longrightarrow>
   lpp_observer_univ_frame (lpc_return_eval nu (states!j)) \<Longrightarrow>
   lpp_check_observer_univ_exit (Fs!j) (states!j)"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)) (lpp_observer_invariant {v. vars_term v={}} specs rest) rest returned i"
proof -
 have simulation: "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution i"
  by (rule lpp_checked_separation_fresh_node_simulation[OF compatible transfer checked source_shape extra])
 have matching: "lp_cut_check_match a (fst (P!c)) match_bindings"
 and fresh: "lpp_check_fresh_univ_clause (fst (P!c)) (snd (P!c)) x y z"
 and head: "lpp_check_separation_head P (nds!i) (contexts!i) a c (LPPSMatching match_bindings)"
  using extra by (auto simp: lpp_check_separation_fresh_def)
 show ?thesis
  apply (rule lpp_observer_frontier_fresh_univ_node_contract[where fuel=fuel and source_returned=source_returned and source_arity=source_arity,
   OF compatible transfer program _ _ simulation source_shape matching fresh clear head covered frontier_shapes _])
  subgoal for j nu by (rule equality_coverage[of j nu]) assumption+
  subgoal for j nu by (rule univ_coverage[of j nu]) assumption+
  subgoal for j nu by (rule exit_coverage[of j nu]) assumption+
  done
qed

ML \<open>
val checked = @{thms lpp_checked_frontier_observer_fresh_univ_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked)) then error "Untrusted checked fresh-univ observer node" else ();
\<close>
end
