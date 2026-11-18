theory LP_Prolog_Observer_Referenced_Node
 imports LP_Prolog_Observer_Rebase_Entry
begin

definition lpp_observer_referenced_node_contract where
 "lpp_observer_referenced_node_contract names operation SP P B U D Q nds states contexts Fs functor_contexts
    node_conditions child_rep J rest returned i =
  (\<forall>eta swaps runtime.
   node_conditions i eta \<longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<longrightarrow>
   lpc_return_scope_word swaps (lpc_reinterface (\<lambda>env x. env (Inl x)) runtime)=lpc_return_eval eta (states!i) \<longrightarrow>
   J runtime \<longrightarrow>
   SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]} \<longrightarrow>
   (\<forall>child u. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    child_rep child u \<longrightarrow> J child \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P B U D)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned) \<longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned)"


lemma lpp_observer_local_to_referenced_node:
 assumes local: "lpp_observer_node_contract names operation SP P B U D Q nds states contexts Fs functor_contexts node_conditions J rest returned i"
 and included: "\<And>child u. lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions
    (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<Longrightarrow> child_rep child u"
 shows "lpp_observer_referenced_node_contract names operation SP P B U D Q nds states contexts Fs functor_contexts node_conditions child_rep J rest returned i"
 using local included
 unfolding lpp_observer_node_contract_def lpp_observer_referenced_node_contract_def by blast

end
