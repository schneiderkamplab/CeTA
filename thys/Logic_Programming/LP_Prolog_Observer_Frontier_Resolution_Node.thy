theory LP_Prolog_Observer_Frontier_Resolution_Node
 imports LP_Prolog_Observer_Frontier_Resolution_Contract
begin

lemma lpp_frontier_observer_resolution_node_contract:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest={}"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_functor_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) a gs c m helper_payload helper_saved k l refreshed next anchors bindings mode outputs (contexts!i) (functor_contexts!i) yes no"
 and source_shape: "states!i=(LPCClause (LPCAtom a#gs) c m,helper_payload)#helper_saved"
 and head_check: "lpp_check_separation_head P (nds!i) (contexts!i) a c witness"
 and success_member: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow> lpcl_target yes\<in>frontier_nodes"
 and failure_member: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow> lpcl_target no\<in>frontier_nodes"
 and success_transport: "mode\<noteq>LPCAlwaysFailure \<Longrightarrow>
   lpcl_target yes<length separation_contexts \<and>
   lpp_check_separation_transport yes_separation (separation_contexts!lpcl_target yes)
    (lp_cut_instance_subst (lpcl_bindings yes))"
 and failure_transport: "mode\<noteq>LPCAlwaysSuccess \<Longrightarrow>
   lpcl_target no<length separation_contexts \<and>
   lpp_check_separation_transport no_separation (separation_contexts!lpcl_target no)
    (lp_cut_instance_subst (lpcl_bindings no))"
 and success_init: "\<And>eta sigma rho.
   lpp_separation_node_conditions separation_contexts i eta \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
   lpp_finite_term (lp_ieval a eta) \<Longrightarrow>
   lpc_mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
    (fst (P!c)) (snd (P!c)) sigma rho \<Longrightarrow>
   list_all (lpp_separation_holds (lp_cut_resolution_env k l eta sigma rho)) yes_separation"
 and failed: "set no_separation \<subseteq> set (separation_contexts!i)"
 and covered: "lpp_check_attached_leaf_slots (map fst specs) rest"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
   (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)) (lpp_observer_invariant {v. vars_term v={}} specs rest) rest returned i"
proof (rule lpp_observer_canonical_node_contract[OF program clear])
 show "\<And>swaps runtime. lpp_observer_invariant {v. vars_term v={}} specs rest runtime \<Longrightarrow>
   lpp_observer_invariant {v. vars_term v={}} specs rest (lpc_return_scope_word swaps runtime)"
  by (simp add: lpp_observer_invariant_scopes[OF clear])
next
 fix eta runtime
 show "lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts) i eta \<longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<longrightarrow>
   lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta (states!i) \<longrightarrow>
   lpp_observer_invariant {v. vars_term v={}} specs rest runtime \<longrightarrow>
   SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]} \<longrightarrow>
   (\<forall>child u. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)) (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<longrightarrow>
    lpp_observer_invariant {v. vars_term v={}} specs rest child \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned) \<longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
 proof (intro impI)
  assume frontier_conditions: "lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts) i eta"
  and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
  and free: "lpc_free_knowledge (set (Fs!i)) eta"
  and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
  and functors: "list_all (lpp_functor_fact_holds names eta) (functor_contexts!i)"
  and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta (states!i)"
  and invariant: "lpp_observer_invariant {v. vars_term v={}} specs rest runtime"
  and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  and lower: "\<forall>child u. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)) (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<longrightarrow>
    lpp_observer_invariant {v. vars_term v={}} specs rest child \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
  have conditions: "lpp_separation_node_conditions separation_contexts i eta"
   using frontier_conditions by (simp add: lpp_observer_frontier_conditions_def)
  have helper_shape: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime =
    (LPCClause (LPCAtom (lp_ieval a eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) c m,
     lpc_return_env helper_payload eta)#lpc_return_eval eta helper_saved"
   using represented by (simp add: source_shape lpc_return_eval_def)
  obtain combined_env combined_saved where runtime_shape: "runtime =
    (LPCClause (LPCAtom (lp_ieval a eta)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) c m,
     combined_env)#combined_saved"
   using helper_shape by (cases runtime) (auto simp: lpc_reinterface_def split: prod.splits)
  have finite_call: "lpp_finite_term (lp_ieval a eta)"
   using invariant by (auto simp: lpp_observer_invariant_def runtime_shape
    lpc_reinterface_def lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)
  have success_separation: "list_all (lpp_separation_holds (lp_cut_resolution_env k l eta sigma rho)) yes_separation"
   if mgu: "lpc_mgu_resolve (lp_ieval a eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)
    (fst (P!c)) (snd (P!c)) sigma rho" for sigma rho
   by (rule success_init[OF conditions known finite_call mgu])
  have failure_separation: "list_all (lpp_separation_holds eta) no_separation"
   using conditions failed by (auto simp: lpp_separation_node_conditions_def list_all_iff)
  show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
  proof (rule lpp_checked_frontier_observer_resolution_contract[where eta=eta and runtime=runtime and specs=specs
    and combined_env=combined_env and combined_saved=combined_saved and names=names and rest=rest,
    OF compatible transfer checked
    success_member failure_member success_transport failure_transport success_separation failure_separation known free observed functors
    head_check runtime_shape represented[unfolded source_shape] covered invariant])
   fix child u
   assume strict: "([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+"
   and module: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    (lpp_observer_frontier_conditions frontier_nodes (lpp_separation_node_conditions separation_contexts)) (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u"
   and child_invariant: "lpp_observer_invariant {v. vars_term v={}} specs rest child"
   show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
    using lower strict module child_invariant by blast
  qed
 qed
qed

ML \<open>
val checked = @{thms lpp_frontier_observer_resolution_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted observer resolution node" else ();
\<close>
end
