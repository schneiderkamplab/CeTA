theory LP_Prolog_Observer_Frontier_Term_Test
 imports LP_Prolog_Observer_Frontier_Test_Action LP_Prolog_Observer_Term_Test
begin

lemma lpp_checked_frontier_observer_term_test:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_term_test T yes_facts no_facts fuel Q nds states contexts Fs functor_contexts nd F source_rows source_context source_functors f a gs helper_payload helper_saved yes no"
    and target_checks: "\<And>holds. holds\<in>set (lpp_var_outcomes f (lpcn_ground nd) a) \<Longrightarrow>
      lpcl_target (if holds then yes else no)\<in>frontier_nodes \<and>
      lpcl_target (if holds then yes else no)<length separation_contexts \<and>
      lpp_check_separation_transport source_separation
       (separation_contexts!lpcl_target (if holds then yes else no))
       (lp_cut_instance_subst (lpcl_bindings (if holds then yes else no)))"
    and separation: "list_all (lpp_separation_holds eta) source_separation"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta source_rows"
 and invariant: "lpp_leaf_stack_invariant leaf_set specs
   (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) event result"
 shows "event=None \<and> (\<exists>tt u swaps.
   lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain runtime None tt \<and>
   result=lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) tt) \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts))
    (lpc_reinterface (\<lambda>env x. env (Inl x)) (lpc_return_scope_word swaps tt)) u \<and>
   lpp_leaf_stack_invariant leaf_set specs
    (lpc_reinterface (\<lambda>env x. env (Inr x)) (lpc_return_scope_word swaps tt)))"
proof -
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?L = "\<lambda>env x. env (Inl x)"
 let ?R = "\<lambda>env x. env (Inr x)"
 let ?C = "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts))"
 have name: "lpp_var_name f"
 and shape: "source_rows=(LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),helper_payload)#helper_saved"
  using checked by (auto simp: lpp_check_functor_term_test_def)
 have projection: "lpc_reinterface ?L runtime=
   (LPCGoals (LPCAtom (LPIFun (LPCUser f) [lp_ieval a eta])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
    lpc_return_env helper_payload eta)#lpc_return_eval eta helper_saved"
  by (simp add: represented shape lpc_return_eval_def)
 obtain env saved where runtime_shape: "runtime=
   (LPCGoals (LPCAtom (LPIFun (LPCUser f) [lp_ieval a eta])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),env)#saved"
  using projection by (cases runtime) (auto simp: lpc_reinterface_def split: prod.splits)
 have active_prefix: "lpc_prefix_active runtime" by (simp add: runtime_shape)
 have local_context: "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   ?C (lpc_return_scope_word swaps ys) u"
  if local_step: "?T (lpc_reinterface ?L runtime) None ys" for ys
 proof -
  have supported: "\<not>lpp_builtin_domain_bad lpp_builtin_signature lpp_univ_source_domain (map fst (lpc_return_eval eta source_rows))"
   by (rule lpp_functor_term_test_domain[OF checked])
  have actual: "lpp_answer_transition P lpp_builtin_signature (lpp_univ_source_builtin names operation)
    (lpc_return_eval eta source_rows) None ys"
   using local_step supported by (simp add: represented lpp_domain_answers_def)
  show ?thesis using lpp_frontier_separation_term_test_sound[OF compatible program checked target_checks separation
   known free observed functors actual] by blast
 qed
 have attached_invariant: "lpp_leaf_stack_invariant leaf_set specs
   (lpc_attach_answers rest (lpc_reinterface ?R runtime))"
  using invariant by (simp add: lpp_leaf_stack_attachment)
 have preserved: "lpp_leaf_stack_invariant leaf_set specs result"
  using lpp_actual_term_test_leaf_stack_step[OF name] step attached_invariant
  by (auto simp: runtime_shape lpc_reinterface_def lpc_attach_answers_def)
 show ?thesis by (rule lpp_observer_step[OF active_prefix step local_context preserved])
qed

ML \<open>
val checked = @{thms lpp_checked_frontier_observer_term_test};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted observer term test" else ();
\<close>
end
