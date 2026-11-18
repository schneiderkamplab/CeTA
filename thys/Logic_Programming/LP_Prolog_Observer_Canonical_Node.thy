theory LP_Prolog_Observer_Canonical_Node
 imports LP_Prolog_Observer_Attached_Scopes
begin

lemma lpp_observer_scope_free_rest_fixed:
 assumes clear: "lpc_rest_scopes rest={}"
 shows "map (lp_cut_scope_goal rename) rest=rest"
proof -
 have each: "lp_cut_scope_goal rename g=g" if "g\<in>set rest" for g
  using clear that by (cases g) auto
 show ?thesis by (rule map_idI) (rule each; assumption)
qed

lemma lpp_observer_canonical_node_contract:
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
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions
     (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<longrightarrow> J child \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P B U D)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned) \<longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
 shows "lpp_observer_node_contract names operation SP P B U D Q nds states contexts Fs functor_contexts
   node_conditions J rest returned i"
 unfolding lpp_observer_node_contract_def
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
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions
     (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<longrightarrow> J child \<longrightarrow>
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

ML \<open>
val checked = @{thms lpp_observer_scope_free_rest_fixed lpp_observer_canonical_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted canonical observer node bridge" else ();
\<close>
end
