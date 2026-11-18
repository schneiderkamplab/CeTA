theory LP_Prolog_Observer_Referenced_Link_Node
 imports LP_Prolog_Observer_Referenced_Canonical
begin

lemma lpp_checked_observer_referenced_link_node:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest={}"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and shape: "states!i=[(LPCGoals gs,source_payload)]"
 and checked: "lpp_check_evaluation_functor_link T fs fuel Q target_nodes target_states target_contexts target_free target_functors
   (nds!i) [(LPCGoals gs,helper_payload)] (lpcn_ground (nds!i)) (lpcn_guards (nds!i)) [] (Fs!i) (contexts!i) (functor_contexts!i) e"
 and member: "lpcl_target e\<in>target_frontier"
 and bound: "lpcl_target e<length target_separation"
 and transport: "lpp_check_separation_transport source_separation (target_separation!lpcl_target e)
   (lp_cut_instance_subst (lpcl_bindings e))"
 and separation: "\<And>eta. node_conditions i eta \<Longrightarrow> list_all (lpp_separation_holds eta) source_separation"
 and included: "\<And>child u. lpp_premised_functor_module_rep names operation SP target_nodes target_states target_contexts target_free target_functors
    (lpp_observer_frontier_conditions target_frontier (lpp_separation_node_conditions target_separation))
    (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<Longrightarrow> child_rep child u"
 shows "lpp_observer_referenced_node_contract names operation SP P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
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
    child_rep child u \<longrightarrow>
    lpp_observer_invariant A specs rest child \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned) \<longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
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
  and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  and lower: "\<forall>child u. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    child_rep child u \<longrightarrow>
    lpp_observer_invariant A specs rest child \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
  have helper_shape: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime =
    [(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),lpc_return_env source_payload eta)]"
   using represented by (simp add: shape lpc_return_eval_def)
  obtain env where runtime_shape: "runtime=[(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),env)]"
   using helper_shape by (cases runtime) (auto simp: lpc_reinterface_def split: prod.splits)
  have rebased: "lpc_reinterface (\<lambda>env x. env (Inl x))
    (lpp_observer_rebase (\<lambda>_ _. lpc_return_env helper_payload eta) runtime) =
    lpc_return_eval eta [(LPCGoals gs,helper_payload)]"
   by (rule lpp_observer_rebase_entry_representation[OF runtime_shape])
  have sep: "list_all (lpp_separation_holds eta) source_separation"
   by (rule separation[OF conditions])
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
  proof (rule lpp_checked_observer_module_link_contract[OF compatible transfer checked member bound transport
    sep equations refl known free observed functors rebased invariant])
   fix child u
   assume strict: "([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+"
   and module: "lpp_premised_functor_module_rep names operation SP target_nodes target_states target_contexts target_free target_functors
    (lpp_observer_frontier_conditions target_frontier (lpp_separation_node_conditions target_separation))
    (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u"
   and inv: "lpp_observer_invariant A specs rest child"
   show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
    using lower strict included[OF module] inv by blast
  qed

 qed
qed

ML \<open>
val checked = @{thms lpp_checked_observer_referenced_link_node};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted referenced observer link node" else ();
\<close>
end
