theory LP_Prolog_Observer_Term_Test_Contract
 imports LP_Prolog_Observer_Unification_Check
begin

lemma lpp_checked_observer_term_test_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_term_test T yes_facts no_facts fuel Q nds states contexts Fs functor_contexts nd F source_rows source_context source_functors f a gs helper_payload helper_saved yes no"
    and empty_targets: "\<And>holds. holds\<in>set (lpp_var_outcomes f (lpcn_ground nd) a) \<Longrightarrow>
      lpcl_target (if holds then yes else no)<length separation_contexts \<and>
      separation_contexts!lpcl_target (if holds then yes else no)=[]"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta source_rows"
 and invariant: "lpp_observer_invariant leaf_set specs rest runtime"
 and lower: "\<And>child u. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<Longrightarrow>
   lpp_observer_invariant leaf_set specs rest child \<Longrightarrow>
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
 have leaf: "lpp_leaf_stack_invariant leaf_set specs (lpc_reinterface ?R runtime)"
 and finite: "lpp_finite_execution (lpc_attach_answers rest (lpc_reinterface ?R runtime))"
  using invariant by (simp_all add: lpp_observer_invariant_def)
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
 obtain child u swaps where silent: "event=None"
 and actual: "result=lpc_attach_answers rest (lpc_reinterface ?R child)"
 and strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
 and rep: "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) (lpc_reinterface ?L (lpc_return_scope_word swaps child)) u"
 and child_leaf: "lpp_leaf_stack_invariant leaf_set specs (lpc_reinterface ?R (lpc_return_scope_word swaps child))"
  using lpp_checked_observer_term_test[OF compatible program checked empty_targets
   known free observed functors represented leaf step] by blast
 have child_finite: "lpp_finite_execution result"
  using step finite by (auto simp: runtime_shape lpc_reinterface_def lpc_attach_answers_def
   lpp_domain_answers_def lpp_univ_term_test_step[OF name]
   lpp_finite_execution_def lpp_finite_goals_def split: if_splits)
 have child_invariant: "lpp_observer_invariant leaf_set specs rest child"
  using child_leaf child_finite actual
  by (simp add: lpp_observer_invariant_def lpp_observer_reinterface_scopes lpp_leaf_stack_scopes)
 have module: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) (lpc_reinterface ?L child) u"
  using rep by (auto simp: lpp_premised_functor_module_rep_def lpp_observer_reinterface_scopes)
 show "event=None \<and> (\<exists>child u. result=lpc_attach_answers rest (lpc_reinterface ?R child) \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) (lpc_reinterface ?L child) u \<and>
   lpp_observer_invariant leaf_set specs rest child)"
  using silent actual strict module child_invariant by blast
qed

ML \<open>
val checked = @{thms lpp_checked_observer_term_test_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted observer term-test contract" else ();
\<close>
end
