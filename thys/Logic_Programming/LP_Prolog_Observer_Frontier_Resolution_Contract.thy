theory LP_Prolog_Observer_Frontier_Resolution_Contract
 imports LP_Prolog_Observer_Frontier_Resolution LP_Prolog_Observer_Resolution_Contract
begin

lemma lpp_checked_frontier_observer_resolution_contract:
  fixes SP :: "string lpp_success_clause list"
  and combined_env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts nd F a gs c m helper_payload helper_saved k l A next anchors bindings mode outputs source_context source_functors yes no"
    and success_member: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow> lpcl_target yes\<in>frontier_nodes"
 and failure_member: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow> lpcl_target no\<in>frontier_nodes"
 and success_transport: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow>
      lpcl_target yes<length separation_contexts \<and>
      lpp_check_separation_transport yes_separation (separation_contexts!lpcl_target yes)
        (lp_cut_instance_subst (lpcl_bindings yes))"
    and failure_transport: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow>
      lpcl_target no<length separation_contexts \<and>
      lpp_check_separation_transport no_separation (separation_contexts!lpcl_target no)
        (lp_cut_instance_subst (lpcl_bindings no))"
    and success_separation: "\<And>sigma rho. lpc_mgu_resolve (lp_ieval a eta)
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) (fst (P!c)) (snd (P!c)) sigma rho \<Longrightarrow>
      list_all (lpp_separation_holds (lp_cut_resolution_env k l eta sigma rho)) yes_separation"
    and failure_separation: "list_all (lpp_separation_holds eta) no_separation"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and head_check: "lpp_check_separation_head P nd source_context a c witness"
 and shape: "runtime=(LPCClause (LPCAtom (lp_ieval a eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) c m,combined_env)#combined_saved"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime =
   lpc_return_eval eta ((LPCClause (LPCAtom a#gs) c m,helper_payload)#helper_saved)"

 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and invariant: "lpp_observer_invariant {u. vars_term u={}} specs rest runtime"
 and lower: "\<And>child u. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)) (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<Longrightarrow>
   lpp_observer_invariant {v. vars_term v={}} specs rest child \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] returned"
proof (rule lpp_observer_silent_contract[OF _ lower])
 fix event result
 let ?L = "\<lambda>env x. env (Inl x)"
 let ?R = "\<lambda>env x. env (Inr x)"
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 assume step: "?T (lpc_attach_answers rest (lpc_reinterface ?R runtime)) event result"
 have leaf: "lpp_leaf_stack_invariant {u. vars_term u={}} specs (lpc_reinterface ?R runtime)"
 and finite: "lpp_finite_execution (lpc_attach_answers rest (lpc_reinterface ?R runtime))"
  using invariant by (simp_all add: lpp_observer_invariant_def)
 have finite_call: "lpp_finite_term (lp_ieval a eta)"
 and finite_rest: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs @
   map (lp_cut_map (\<lambda>t. lp_ieval t (?R combined_env))) rest)"
  using finite by (auto simp: shape lpc_reinterface_def lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)
 obtain child u swaps where silent: "event=None"
 and actual: "result=lpc_attach_answers rest (lpc_reinterface ?R child)"
 and strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
 and rep: "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)) (lpc_reinterface ?L (lpc_return_scope_word swaps child)) u"
 and child_leaf: "lpp_leaf_stack_invariant {v. vars_term v={}} specs (lpc_reinterface ?R (lpc_return_scope_word swaps child))"
  using lpp_checked_frontier_observer_resolution[OF compatible program checked success_member failure_member success_transport failure_transport
    success_separation failure_separation known free observed functors head_check shape represented
    finite_call finite_rest covered leaf step] by blast
 have base: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCClause (LPCAtom (lp_ieval a eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) c m,
    ?R combined_env)#lpc_reinterface ?R combined_saved)) event result"
  using step by (auto simp: shape lpc_reinterface_def lpc_attach_answers_def intro: lpp_observer_clause_base)
 have child_finite: "lpp_finite_execution result"
  by (rule lpp_checked_head_attached_finite_step[OF head_check known observed base])
   (use finite in \<open>simp add: shape lpc_reinterface_def\<close>)
 have child_invariant: "lpp_observer_invariant {v. vars_term v={}} specs rest child"
  using child_leaf child_finite actual
  by (simp add: lpp_observer_invariant_def lpp_observer_reinterface_scopes lpp_leaf_stack_scopes)
 have module: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)) (lpc_reinterface ?L child) u"
  using rep by (auto simp: lpp_premised_functor_module_rep_def lpp_observer_reinterface_scopes)
 show "event=None \<and> (\<exists>child u. result=lpc_attach_answers rest (lpc_reinterface ?R child) \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)) (lpc_reinterface ?L child) u \<and>
   lpp_observer_invariant {v. vars_term v={}} specs rest child)"
  using silent actual strict module child_invariant by blast
qed

ML \<open>
val checked = @{thms lpp_checked_frontier_observer_resolution_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted observer resolution contract" else ();
\<close>
end
