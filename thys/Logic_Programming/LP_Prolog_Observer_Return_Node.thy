theory LP_Prolog_Observer_Return_Node
 imports LP_Prolog_Observer_Return_Boundary LP_Prolog_Observer_Referenced_Canonical
begin

lemma lpp_observer_single_return_referenced_node:
 assumes program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest={}"
 and shape: "states!i=[(LPCGoals [],payload)]"
 and continuation: "\<And>eta env. node_conditions i eta \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<Longrightarrow>
   (\<lambda>x. env (Inl x))=lpc_return_env payload eta \<Longrightarrow>
   list_all (\<lambda>(slot,tree). lpp_runtime_leaf_effect A tree (env (Inr slot))) specs \<Longrightarrow>
   lpp_finite_execution [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x (\<lambda>i. env (Inr i)))) rest),\<lambda>i. env (Inr i))] \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x (\<lambda>i. env (Inr i)))) rest),\<lambda>i. env (Inr i))]
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
 shows "lpp_observer_referenced_node_contract names operation SP P B U D Q nds states contexts Fs functor_contexts
   node_conditions child_rep (lpp_observer_invariant A specs rest) rest returned i"
proof (rule lpp_observer_referenced_canonical_node_contract[OF program clear])
 show "\<And>swaps runtime. lpp_observer_invariant A specs rest runtime \<Longrightarrow>
   lpp_observer_invariant A specs rest (lpc_return_scope_word swaps runtime)"
  by (simp add: lpp_observer_invariant_scopes[OF clear])
next
 fix eta runtime
 show "node_conditions i eta \<longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<longrightarrow>
   lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta (states!i) \<longrightarrow>
   lpp_observer_invariant A specs rest runtime \<longrightarrow>
   SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]} \<longrightarrow>
   (\<forall>child u. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    child_rep child u \<longrightarrow> lpp_observer_invariant A specs rest child \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P B U D)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned) \<longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
 proof (intro impI)
  assume conditions: "node_conditions i eta"
  and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
  and free: "lpc_free_knowledge (set (Fs!i)) eta"
  and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
  and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
  and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta (states!i)"
  and invariant: "lpp_observer_invariant A specs rest runtime"
  have exact: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=[(LPCGoals [],lpc_return_env payload eta)]"
   using represented by (simp add: shape lpc_return_eval_def)
  show "lp_answer_contract (lpp_domain_answers P B U D)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
   by (rule lpp_observer_single_return_joint_contract[OF exact invariant])
    (rule continuation[OF conditions known free observed functors]; assumption)
 qed
qed

end
