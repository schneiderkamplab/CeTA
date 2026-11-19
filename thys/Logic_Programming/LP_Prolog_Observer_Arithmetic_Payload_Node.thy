theory LP_Prolog_Observer_Arithmetic_Payload_Node
 imports LP_Prolog_Arithmetic_Target_Payload
begin

theorem lpp_observer_arithmetic_payload_node_contract:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest={}"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_observed_functor_link T fs fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) a e gs helper_payload helper_saved result_var middle"
 and source_shape: "states!i=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),helper_payload)#helper_saved"
 and initial_ground: "vars_term initial_parameter = {}"
 and target_shape: "states!lpcl_target middle =
   (LPCGoals (LPCUnify (Var output_slot) (Var scalar_slot)#target_rest),target_payload)#target_saved"
 and source_coordinate: "payload_slot<length helper_payload" "helper_payload!payload_slot = parameter_term"
 and target_coordinate: "payload_slot<length target_payload" "target_payload!payload_slot = Var parameter_slot"
 and incoming_parameter: "\<And>eta. node_conditions i eta \<Longrightarrow>
   lpp_runtime_parameter initial_parameter (lp_ieval parameter_term eta)"
 and target_init: "\<And>eta combined_env combined_saved value_name rho. node_conditions i eta \<Longrightarrow>
   lpp_stable_scalar_evaluation operation (lp_ieval e eta) (LPIFun (LPCUser value_name) []) \<Longrightarrow>
   lpc_reinterface (\<lambda>env x. env (Inl x))
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser value_name) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved)
     =lpc_return_eval rho (states!lpcl_target middle) \<Longrightarrow>
   ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],
     [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho \<Longrightarrow>
   lpc_free_knowledge (set (Fs!lpcl_target middle)) rho \<Longrightarrow>
   lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho \<Longrightarrow>
   list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle) \<Longrightarrow>
   lpp_observer_invariant leaf_set specs rest ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser value_name) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved) \<Longrightarrow>
   rho output_slot = lp_ieval a eta \<Longrightarrow>
   rho scalar_slot = LPIFun (LPCUser value_name) [] \<Longrightarrow>
   lpp_runtime_parameter initial_parameter (rho scalar_slot) \<Longrightarrow>
   lpp_runtime_parameter initial_parameter (rho parameter_slot) \<Longrightarrow>
   node_conditions (lpcl_target middle) rho"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature
   (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
   node_conditions (lpp_observer_invariant leaf_set specs rest) rest returned i"
proof (rule lpp_observer_canonical_node_contract[OF program clear])
 show "\<And>swaps runtime. lpp_observer_invariant leaf_set specs rest runtime \<Longrightarrow>
   lpp_observer_invariant leaf_set specs rest (lpc_return_scope_word swaps runtime)"
  by (simp add: lpp_observer_invariant_scopes[OF clear])
next
 fix eta runtime
 show "node_conditions i eta \<longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<longrightarrow>
   lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta (states!i) \<longrightarrow>
   lpp_observer_invariant leaf_set specs rest runtime \<longrightarrow>
   SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]} \<longrightarrow>
   (\<forall>child u. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<longrightarrow>
    lpp_observer_invariant leaf_set specs rest child \<longrightarrow>
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
  and invariant: "lpp_observer_invariant leaf_set specs rest runtime"
  and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  and lower: "\<forall>child u. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<longrightarrow>
    lpp_observer_invariant leaf_set specs rest child \<longrightarrow>
    lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
  have helper_shape: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime =
    (LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [lp_ieval a eta,lp_ieval e eta])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
     lpc_return_env helper_payload eta)#lpc_return_eval eta helper_saved"
   using represented by (simp add: source_shape lpc_return_eval_def)
  obtain combined_env combined_saved where runtime_shape: "runtime =
    (LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [lp_ieval a eta,lp_ieval e eta])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
     combined_env)#combined_saved"
   using helper_shape by (cases runtime) (auto simp: lpc_reinterface_def split: prod.splits)
  have payload_interface: "(\<lambda>x. combined_env (Inl x))=lpc_return_env helper_payload eta"
   using helper_shape runtime_shape by (simp add: lpc_reinterface_def)
  have incoming: "lpp_runtime_parameter initial_parameter (combined_env (Inl payload_slot))"
   using incoming_parameter[OF conditions] fun_cong[OF payload_interface, of payload_slot] source_coordinate
   by (simp add: lpc_return_env_def)
  have payload_parameter: "lpp_runtime_parameter initial_parameter (rho parameter_slot)"
   if represented_target: "lpc_reinterface (\<lambda>env x. env (Inl x))
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser value_name) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved)
     =lpc_return_eval rho (states!lpcl_target middle)" for rho value_name
   using lpp_arithmetic_target_payload_parameter[where project="\<lambda>env x. env (Inl x)" and slot=payload_slot and parameter_slot=parameter_slot, OF represented_target[unfolded target_shape] target_coordinate(1) target_coordinate(2) incoming] by blast
  have coordinates: "rho output_slot = lp_ieval a eta \<and>
    rho scalar_slot = LPIFun (LPCUser value_name) [] \<and>
    lpp_runtime_parameter initial_parameter (rho scalar_slot)"
   if represented_target: "lpc_reinterface (\<lambda>env x. env (Inl x))
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser value_name) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved)
     =lpc_return_eval rho (states!lpcl_target middle)" for rho value_name
   by (rule lpp_arithmetic_target_parameter[OF represented_target[unfolded target_shape] initial_ground])
  show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
  proof (rule lpp_checked_conditioned_is_invariant_contract[
    where eta=eta and runtime=runtime and specs=specs and node_conditions=node_conditions
    and combined_env=combined_env and combined_saved=combined_saved and names=names and rest=rest,
    OF compatible transfer checked known free observed functors runtime_shape represented invariant])
   show "\<And>value_name rho.
   lpp_stable_scalar_evaluation operation (lp_ieval e eta) (LPIFun (LPCUser value_name) []) \<Longrightarrow>
   lpc_reinterface (\<lambda>env x. env (Inl x))
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser value_name) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved)
     =lpc_return_eval rho (states!lpcl_target middle) \<Longrightarrow>
   ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],
     [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho \<Longrightarrow>
   lpc_free_knowledge (set (Fs!lpcl_target middle)) rho \<Longrightarrow>
   lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho \<Longrightarrow>
   list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle) \<Longrightarrow>
   lpp_observer_invariant leaf_set specs rest ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser value_name) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved) \<Longrightarrow> node_conditions (lpcl_target middle) rho"
    by (metis target_init[OF conditions] coordinates payload_parameter)
  next
   fix child u
   assume strict: "([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+"
   and module: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u"
   and child_invariant: "lpp_observer_invariant leaf_set specs rest child"
   show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
   proof (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict]])
    show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
     (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
     using lower strict module child_invariant by blast
   qed
  qed
 qed
qed

ML \<open>
val checked = @{thms lpp_observer_arithmetic_payload_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted arithmetic node" else ();
\<close>
end
