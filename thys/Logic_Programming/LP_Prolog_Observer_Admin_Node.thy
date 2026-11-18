theory LP_Prolog_Observer_Admin_Node
 imports LP_Prolog_Observer_Context_Actions
begin

lemma lpp_checked_observer_admin_node:
 fixes SP :: "string lpp_success_clause list"
 assumes program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest={}"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_admin_node T fs fuel Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) returned_symbol arity expected_event next e"
 and bound: "lpcl_target e<length separation_contexts"
 and transport: "lpp_check_separation_transport (separation_contexts!i) (separation_contexts!lpcl_target e)
   (lp_cut_instance_subst (lpcl_bindings e))"
 and simple: "lpp_simple_control_frame (states!i)"
 and no_builtin: "lpp_no_builtin_frame (states!i)"
 and source_active: "lpc_prefix_active (states!i)"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
   (lpp_separation_node_conditions separation_contexts) (lpp_observer_invariant A specs rest) rest returned i"
proof (rule lpp_observer_canonical_node_contract[OF program clear])
 show "\<And>swaps runtime. lpp_observer_invariant A specs rest runtime \<Longrightarrow>
   lpp_observer_invariant A specs rest (lpc_return_scope_word swaps runtime)"
  by (simp add: lpp_observer_invariant_scopes[OF clear])
next
 fix eta runtime
 show "lpp_separation_node_conditions separation_contexts i eta \<longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<longrightarrow>
   lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta (states!i) \<longrightarrow>
   lpp_observer_invariant A specs rest runtime \<longrightarrow>
   SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]} \<longrightarrow>
   (\<forall>child u. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     (lpp_separation_node_conditions separation_contexts) (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<longrightarrow>
    lpp_observer_invariant A specs rest child \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned) \<longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
 proof (intro impI)
  assume conditions: "lpp_separation_node_conditions separation_contexts i eta"
  and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
  and free: "lpc_free_knowledge (set (Fs!i)) eta"
  and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
  and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
  and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta (states!i)"
  and invariant: "lpp_observer_invariant A specs rest runtime"
  and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  and lower: "\<forall>child u. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     (lpp_separation_node_conditions separation_contexts) (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<longrightarrow>
    lpp_observer_invariant A specs rest child \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
  have separated: "list_all (lpp_separation_holds eta) (separation_contexts!i)"
   using conditions by (simp add: lpp_separation_node_conditions_def)
  have active_eval: "lpc_prefix_active (lpc_return_eval eta (states!i))"
   using source_active by (cases "states!i" rule: lpc_prefix_active.cases) (simp_all add: lpc_return_eval_def)
  have active: "lpc_prefix_active runtime"
   using active_eval represented by (metis lpp_observer_reindex_active)
  show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
  proof (rule lpp_observer_simple_contract[OF represented simple no_builtin active invariant])
   fix ys
   assume actual: "lpc_answer_transition P (lpc_return_eval eta (states!i)) None ys"
   show "\<exists>u swaps. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_premised_functor_rep names operation SP nds states contexts Fs functor_contexts
     (lpp_separation_node_conditions separation_contexts) (lpc_return_scope_word swaps ys) u"
    using lpp_context_separation_admin_node_sound[OF compatible transfer checked bound transport separated known free observed functors actual] by blast
  next
   fix child u
   assume strict: "([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+"
   and module: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_separation_node_conditions separation_contexts) (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u"
   and child_invariant: "lpp_observer_invariant A specs rest child"
   show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
    using lower strict module child_invariant by blast
  qed
 qed
qed

ML \<open>
val checked = @{thms lpp_checked_observer_admin_node};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted checked observer administrative node" else ();
\<close>
end
