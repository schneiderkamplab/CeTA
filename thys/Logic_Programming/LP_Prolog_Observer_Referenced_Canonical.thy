theory LP_Prolog_Observer_Referenced_Canonical
 imports LP_Prolog_Observer_Family
begin

lemma lpp_observer_referenced_canonical_node_contract:
 assumes program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest={}"
 and scopes: "\<And>swaps runtime. J runtime \<Longrightarrow> J (lpc_return_scope_word swaps runtime)"
 and canonical: "\<And>eta runtime.
   node_conditions i eta \<longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<longrightarrow>
   lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta (states!i) \<longrightarrow>
   J runtime \<longrightarrow>
   SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]} \<longrightarrow>
   (\<forall>child u. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    child_rep child u \<longrightarrow> J child \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P B U D)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned) \<longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
 shows "lpp_observer_referenced_node_contract names operation SP P B U D Q nds states contexts Fs functor_contexts
   node_conditions child_rep J rest returned i"
 unfolding lpp_observer_referenced_node_contract_def
proof (intro allI impI)
 fix eta swaps runtime
 assume conditions: "node_conditions i eta"
 and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
 and free: "lpc_free_knowledge (set (Fs!i)) eta"
 and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
 and shape: "lpc_return_scope_word swaps (lpc_reinterface (\<lambda>env x. env (Inl x)) runtime)=lpc_return_eval eta (states!i)"
 and invariant: "J runtime"
 and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
 and lower: "\<forall>child u. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    child_rep child u \<longrightarrow> J child \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P B U D)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
 have exact: "lpc_reinterface (\<lambda>env x. env (Inl x)) (lpc_return_scope_word swaps runtime)=lpc_return_eval eta (states!i)"
  using shape by (simp add: lpp_observer_reinterface_scopes)
 have result: "lp_answer_contract (lpp_domain_answers P B U D)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) (lpc_return_scope_word swaps runtime)))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
  using canonical[of eta "lpc_return_scope_word swaps runtime"] conditions known free observed functors exact
    scopes[OF invariant] residual lower by blast
 show "lp_answer_contract (lpp_domain_answers P B U D)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
  by (rule lpp_observer_scoped_contract_restore[OF program _ result])
   (rule lpp_observer_scope_free_rest_fixed[OF clear])
qed

end
