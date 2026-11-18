theory LP_Prolog_Observer_Checked_Frontier_Block
 imports LP_Prolog_Observer_Fresh_Univ_Exit
begin

lemma lpp_checked_frontier_fresh_univ_observer_contract:
 fixes SP :: "string lpp_success_clause list"
 and combined_env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
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
     (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned arity
     (LPPFUniv value_var name_var args_var middle facts) \<and>
    lpp_check_separation_univ separation_contexts i (states!i) name_var args_var middle pair_symbol output_name output_args"
 and resolution: "lpp_observer_node_simulation names operation SP P Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) lpp_finite_execution i"
 and template_shape: "states!i=((LPCClause (LPCAtom a#gs) c m,active)#saved)"
 and matching: "lp_cut_check_match a (fst (P!c)) bindings"
 and fresh: "lpp_check_fresh_univ_clause (fst (P!c)) (snd (P!c)) x y z"
 and conditions: "lpp_separation_node_conditions separation_contexts i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and finite: "lpp_finite_execution (lpc_return_eval eta (states!i))"
 and head: "lpp_check_separation_head P (nds!i) (contexts!i) a c (LPPSMatching bindings)"
 and runtime_shape: "runtime=(LPCClause (LPCAtom (lp_ieval a eta)#runtime_goals) c m,combined_env)#combined_saved"
 and helper_shape: "lpc_reinterface (\<lambda>env slot. env (Inl slot)) runtime=lpc_return_eval eta (states!i)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and invariant: "lpp_observer_invariant {v. vars_term v={}} specs rest runtime"
 and frontier_shapes: "lpp_check_observer_frontier_shapes frontier_nodes states"
 and exit_coverage: "\<And>j (nu :: string\<Rightarrow>(string lp_cut_symbol,string) lp_iterm). j<length nds \<Longrightarrow>
   lpp_observer_univ_frame (lpc_return_eval nu (states!j)) \<Longrightarrow>
   lpp_check_observer_univ_exit (Fs!j) (states!j)"
 and lower: "\<And>child u.
   ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts))
    (lpc_reinterface (\<lambda>env slot. env (Inl slot)) child) u \<Longrightarrow>
   lpp_observer_invariant {v. vars_term v={}} specs rest child \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) child)) (lp_ild Q) u final_return"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env slot. env (Inr slot)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] final_return"
proof (rule lpp_checked_fresh_univ_observer_contract[where node_conditions="lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)",
 OF head fresh known observed runtime_shape covered invariant _ lower])
 fix helper_middle helper_result
 assume first_step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
    (lpc_reinterface (\<lambda>env slot. env (Inl slot)) runtime) None helper_middle"
 and second_step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
    helper_middle None helper_result"
 have simulated: "(None :: (nat\<Rightarrow>(string lp_cut_symbol,string) lp_iterm) option)=None \<and> (None :: (nat\<Rightarrow>(string lp_cut_symbol,string) lp_iterm) option)=None \<and> (helper_result=[] \<or> (\<exists>u.
   ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) helper_result u))"
  apply (rule lpp_checked_fresh_univ_source_block[where fuel=fuel and returned=returned and arity=arity,
    OF compatible transfer program _ _ resolution template_shape matching fresh conditions known free observed functors finite
     first_step[unfolded helper_shape] second_step])
  subgoal for j nu by (rule equality_coverage[of j nu]) assumption+
  subgoal for j nu by (rule univ_coverage[of j nu]) assumption+
  done
 have exit_shape: "\<not>lpp_observer_internal_frame helper_result"
  apply (rule lpp_checked_fresh_univ_exit[OF program _ resolution template_shape matching fresh
   conditions known free observed functors finite first_step[unfolded helper_shape] second_step])
  subgoal for j nu by (rule exit_coverage[of j nu]) assumption+
  done
 have lift: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)) helper_result u"
  if child_rep: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) helper_result u" for u
  by (rule lpp_observer_exit_frontier_rep[OF frontier_shapes child_rep exit_shape])
 show "helper_result=[] \<or> (\<exists>u.
   ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)) helper_result u)"
  using simulated lift by blast

qed

ML \<open>
val checked = @{thms lpp_checked_frontier_fresh_univ_observer_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked)) then error "Untrusted assembled fresh-univ observer contract" else ();
\<close>
end
