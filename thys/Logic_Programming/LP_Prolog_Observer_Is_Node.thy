theory LP_Prolog_Observer_Is_Node
 imports LP_Prolog_Observer_Is_Contract
begin

lemma lpp_checked_observer_is_node_contract:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest={}"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_observed_functor_link T fs fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) a e gs helper_payload helper_saved result_var middle"
 and bounds: "lpcl_target middle<length nds" "lpcl_target middle<length states"
   "lpcl_target middle<length contexts" "lpcl_target middle<length Fs"
   "lpcl_target middle<length functor_contexts"
 and child_conditions: "\<And>rho. node_conditions (lpcl_target middle) rho"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
   node_conditions (lpp_observer_invariant A specs rest) rest returned i"
proof (rule lpp_observer_canonical_node_contract[OF program clear])
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
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<longrightarrow>
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
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<longrightarrow>
    lpp_observer_invariant A specs rest child \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
  have shape: "states!i=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),helper_payload)#helper_saved"
   using checked by (simp add: lpp_check_observed_functor_link_def)
  have helper_shape: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime =
    (LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [lp_ieval a eta,lp_ieval e eta])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
     lpc_return_env helper_payload eta)#lpc_return_eval eta helper_saved"
   using represented by (simp add: shape lpc_return_eval_def)
  obtain combined_env combined_saved where runtime_shape: "runtime =
    (LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [lp_ieval a eta,lp_ieval e eta])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
     combined_env)#combined_saved"
   using helper_shape by (cases runtime) (auto simp: lpc_reinterface_def split: prod.splits)
  show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
  proof (rule lpp_checked_observer_is_contract[where node_conditions=node_conditions and eta=eta and runtime=runtime,
    OF compatible transfer checked bounds child_conditions known free observed functors runtime_shape represented invariant])
   fix child u
   assume strict: "([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+"
   and module: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u"
   and child_invariant: "lpp_observer_invariant A specs rest child"
   show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
    using lower strict module child_invariant by blast
  qed
 qed
qed

ML \<open>
val checked = @{thms lpp_checked_observer_is_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted observer term-test node" else ();
\<close>
end
