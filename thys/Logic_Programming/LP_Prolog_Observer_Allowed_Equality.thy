theory LP_Prolog_Observer_Allowed_Equality
 imports LP_Prolog_Observer_Ground_Equality LP_Prolog_Attached_Allowed_Equality
begin

lemma lpp_checked_observer_allowed_equality:
  fixes SP :: "string lpp_success_clause list"
  and combined_env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts nd F a b gs helper_payload helper_saved k l next mode outputs source_context source_functors yes no"
    and success_transport: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow>
      lpcl_target yes<length separation_contexts \<and>
      lpp_check_separation_transport yes_separation (separation_contexts!lpcl_target yes)
        (lp_cut_instance_subst (lpcl_bindings yes))"
    and failure_transport: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow>
      lpcl_target no<length separation_contexts \<and>
      lpp_check_separation_transport no_separation (separation_contexts!lpcl_target no)
        (lp_cut_instance_subst (lpcl_bindings no))"
    and success_separation: "\<And>sigma. lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta)
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma \<Longrightarrow>
      list_all (lpp_separation_holds (lp_cut_resolution_env k l eta sigma eta)) yes_separation"
    and failure_separation: "list_all (lpp_separation_holds eta) no_separation"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and ground: "vars_term b \<subseteq> set (lpcn_ground nd) \<union> lpp_source_context_ground source_context"
 and selected_free: "lp_ieval a eta=LPIVar x"
 and replacement: "lp_ieval b eta=lp_ieval replacement_template LPIVar"
 and allowed: "replacement_template\<in>A"
 and ground_templates: "\<And>v. v\<in>A \<Longrightarrow> vars_term v={}"
 and shape: "runtime=(LPCGoals (LPCUnify (lp_ieval a eta) (lp_ieval b eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime =
   lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),helper_payload)#helper_saved)"
 and finite_call: "lpp_finite_term (lp_ieval a eta)"
 and finite_rest: "lpp_finite_goals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs @
   map (lp_cut_map (\<lambda>t. lp_ieval t (\<lambda>x. combined_env (Inr x)))) rest)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 and invariant: "lpp_leaf_stack_invariant A specs
   (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
 and step: "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) event result"
 shows "event=None \<and> (\<exists>tt u swaps.
   lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain runtime None tt \<and>
   result=lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) tt) \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts)
    (lpc_reinterface (\<lambda>env x. env (Inl x)) (lpc_return_scope_word swaps tt)) u \<and>
   lpp_leaf_stack_invariant A specs
    (lpc_reinterface (\<lambda>env x. env (Inr x)) (lpc_return_scope_word swaps tt)))"
proof -
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?L = "\<lambda>env x. env (Inl x)"
 let ?R = "\<lambda>env x. env (Inr x)"
 have active_prefix: "lpc_prefix_active runtime" by (simp add: shape)
 obtain tt where silent: "event=None" and joint: "?T runtime None tt"
 and helper_step: "?T (lpc_reinterface ?L runtime) None (lpc_reinterface ?L tt)"
 and returned: "result=lpc_attach_answers rest (lpc_reinterface ?R tt)"
  using lpp_attached_observer_product_step[OF active_prefix step] by blast
 have helper_base: "lpc_answer_transition P
   (lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),helper_payload)#helper_saved))
   None (lpc_reinterface ?L tt)"
  using helper_step[unfolded represented]
  by (auto simp: lpc_return_eval_def intro: lpp_observer_equality_base)
 obtain u swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
 and next_context: "lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts)
   (lpc_return_scope_word swaps (lpc_reinterface ?L tt)) u"
  using lpp_separation_functor_equality_node_sound[OF compatible program checked
   success_transport failure_transport success_separation failure_separation known free observed functors helper_base] by blast
 have caller_base: "lpc_answer_transition P
   (lpc_attach_answers rest ((LPCGoals (LPCUnify (lp_ieval a eta) (lp_ieval b eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
     ?R combined_env)#lpc_reinterface ?R combined_saved)) event result"
  using step by (auto simp: shape lpc_reinterface_def lpc_attach_answers_def intro: lpp_observer_equality_base)
 have caller_invariant: "lpp_leaf_stack_invariant A specs result"
  by (rule lpp_attached_allowed_equality_leaf_base_step[OF caller_base _ finite_rest selected_free replacement allowed ground_templates covered])
   (use invariant in \<open>simp add: shape lpc_reinterface_def\<close>)
 show ?thesis by (intro conjI silent exI[of _ tt] exI[of _ u] exI[of _ swaps])
  (use joint returned strict next_context caller_invariant in
   \<open>simp_all add: lpp_observer_reinterface_scopes lpp_leaf_stack_scopes lpp_leaf_stack_attachment\<close>)
qed

ML \<open>
val checked = @{thms lpp_checked_observer_allowed_equality};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted observer allowed equality" else ();
\<close>
end
