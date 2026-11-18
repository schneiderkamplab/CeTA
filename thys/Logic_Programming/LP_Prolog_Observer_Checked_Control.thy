theory LP_Prolog_Observer_Checked_Control
 imports LP_Prolog_Observer_Control
begin

lemma lpp_checked_observer_admin:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_admin_node T fs fuel Q nds states contexts Fs functor_contexts nd F source_rows source_context source_functors returned arity expected_event next e"
    and separation_bound: "lpcl_target e<length separation_contexts"
    and empty: "separation_contexts!lpcl_target e=[]"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta source_rows"
 and simple: "lpp_simple_control_frame source_rows"
 and clear: "lpp_no_builtin_frame source_rows"
 and active_prefix: "lpc_prefix_active runtime"
 and invariant: "lpp_leaf_stack_invariant leaf_set specs
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
   lpp_leaf_stack_invariant leaf_set specs
    (lpc_reinterface (\<lambda>env x. env (Inr x)) (lpc_return_scope_word swaps tt)))"
proof (rule lpp_observer_control_step[OF represented simple clear active_prefix _ invariant step])
 fix ys
 assume actual: "lpc_answer_transition P (lpc_return_eval eta source_rows) None ys"
 show "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) (lpc_return_scope_word swaps ys) u"
  using lpp_empty_separation_admin_node_sound[OF compatible program checked separation_bound empty
   known free observed functors actual] by blast
qed

lemma lpp_checked_observer_case:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_functor_case_node T fs fuel P Q nds states contexts Fs functor_contexts nd F source_context source_functors m f ts gs helper_payload helper_saved e"
    and separation_bound: "lpcl_target e<length separation_contexts"
    and empty: "separation_contexts!lpcl_target e=[]"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and shape: "source_rows=(LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),helper_payload)#helper_saved"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta source_rows"
 and simple: "lpp_simple_control_frame source_rows"
 and clear: "lpp_no_builtin_frame source_rows"
 and active_prefix: "lpc_prefix_active runtime"
 and invariant: "lpp_leaf_stack_invariant leaf_set specs
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
   lpp_leaf_stack_invariant leaf_set specs
    (lpc_reinterface (\<lambda>env x. env (Inr x)) (lpc_return_scope_word swaps tt)))"
proof (rule lpp_observer_control_step[OF represented simple clear active_prefix _ invariant step])
 fix ys
 assume actual: "lpc_answer_transition P (lpc_return_eval eta source_rows) None ys"
 show "\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
   lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) (lpc_return_scope_word swaps ys) u"
  using lpp_empty_separation_case_node_sound[OF compatible program checked separation_bound empty
   known free observed functors actual[unfolded shape]] by blast
qed

ML \<open>
val checked = @{thms lpp_checked_observer_admin lpp_checked_observer_case};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checked observer control" else ();
\<close>
end
