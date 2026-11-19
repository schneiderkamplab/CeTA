theory LP_Prolog_Observer_Output_Arithmetic_Node
 imports LP_Prolog_Observer_Output_Copy_Node LP_Prolog_Observer_Arithmetic_Node
begin

text \<open>Arithmetic normalization changes the selected goal but retains the
shared environment and all saved alternatives. Carry the output equality with
the restricted leaf and finite invariant into the represented equality node.\<close>

lemma lpp_checked_conditioned_is_output_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_observed_functor_link T fs fuel P Q nds states contexts Fs functor_contexts nd F source_rows source_context source_functors a e gs helper_payload helper_saved result_var middle"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and runtime_shape: "runtime=(LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [lp_ieval a eta,lp_ieval e eta])#
    map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta source_rows"
 and invariant: "lpp_observer_output_invariant leaf_set specs rest oi hi runtime"
 and target_init: "\<And>value_name rho.
   lpp_stable_scalar_evaluation operation (lp_ieval e eta) (LPIFun (LPCUser value_name) []) \<Longrightarrow>
   lpc_reinterface (\<lambda>env x. env (Inl x))
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser value_name) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved)
     =lpc_return_eval rho (states!lpcl_target middle) \<Longrightarrow>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],
     [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho \<Longrightarrow>
   lpc_free_knowledge (set (Fs!lpcl_target middle)) rho \<Longrightarrow>
   lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho \<Longrightarrow>
   list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle) \<Longrightarrow>
   lpp_observer_output_invariant leaf_set specs rest oi hi ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser value_name) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved) \<Longrightarrow> node_conditions (lpcl_target middle) rho"
 and lower: "\<And>child u. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions
    (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<Longrightarrow>
   lpp_observer_output_invariant leaf_set specs rest oi hi child \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) R subject returned"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) R subject returned"
proof -
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?L = "\<lambda>env x. env (Inl x)"
 let ?R = "\<lambda>env x. env (Inr x)"
 let ?norm = "\<lambda>f. (LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved"
 have expression_finite: "lpp_finite_term (lp_ieval e eta)"
  using invariant by (auto simp: lpp_observer_output_invariant_def lpp_observer_output_alias_def lpp_observer_invariant_def runtime_shape lpc_reinterface_def
    lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)
 have domain: "lpp_finite_source_domain ''2:is'' [lp_ieval a eta,lp_ieval e eta]"
  by (rule lpp_finite_is_source_domain[OF expression_finite])
 have source_shape: "source_rows=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),helper_payload)#helper_saved"
  using checked by (simp add: lpp_check_observed_functor_link_def)
 have interfaces: "?L combined_env=lpc_return_env helper_payload eta"
   "lpc_reinterface ?L combined_saved=lpc_return_eval eta helper_saved"
  using represented by (auto simp: runtime_shape source_shape lpc_reinterface_def lpc_return_eval_def)
 have normalized_contract: "lp_answer_contract ?T (lpc_attach_answers rest (lpc_reinterface ?R (?norm f))) R subject returned"
  if evaluated: "lpp_stable_scalar_evaluation operation (lp_ieval e eta) (LPIFun (LPCUser f) [])" for f
 proof -
  obtain rho where same: "((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env helper_payload eta)#lpc_return_eval eta helper_saved)=lpc_return_eval rho (states!lpcl_target middle)"
  and strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
     [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>(lp_ild Q)\<^sup>+"
  and child_known: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
  and child_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
  and child_observed: "lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho"
  and child_functors: "list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle)"
   using lpp_checked_is_normalization_witness[OF compatible program checked domain known free observed functors evaluated] by blast
  have helper_projection: "lpc_reinterface ?L (?norm f)=lpc_return_eval rho (states!lpcl_target middle)"
   using same interfaces by (simp add: lpc_reinterface_def)
  have caller_invariant: "lpp_observer_output_invariant leaf_set specs rest oi hi (?norm f)"
   using invariant by (auto simp: lpp_observer_output_invariant_def lpp_observer_output_alias_def lpp_observer_invariant_def runtime_shape lpc_reinterface_def lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def lpp_leaf_stack_invariant_def)
  have conditions: "node_conditions (lpcl_target middle) rho"
   by (rule target_init[OF evaluated helper_projection strict child_known child_free child_observed child_functors caller_invariant])
  have bounds: "lpcl_target middle<length nds" "lpcl_target middle<length states"
    "lpcl_target middle<length contexts" "lpcl_target middle<length Fs" "lpcl_target middle<length functor_contexts"
   using checked by (auto simp: lpp_check_observed_functor_link_def lpp_check_evaluation_functor_link_def
     lpp_check_evaluation_link_def lpc_check_return_table_link_def lpc_check_return_link_def lpc_check_link_def)
  have module: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts node_conditions
    (lpc_reinterface ?L (?norm f)) [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))]"
   unfolding helper_projection
   unfolding lpp_premised_functor_module_rep_def
   apply (rule exI[of _ "[]"])
   apply (simp only: lpc_return_scope_word.simps)
   unfolding lpp_premised_functor_rep_def
   apply (rule exI[of _ "lpcl_target middle"], rule exI[of _ rho])
   using bounds child_known child_free child_observed conditions child_functors by simp
  show ?thesis by (rule lower[OF strict module caller_invariant])
 qed
 show ?thesis
  unfolding runtime_shape
  apply (simp add: lpc_reinterface_def lpc_attach_answers_def)
  apply (rule lpp_univ_evaluation_domain_contract[OF domain])
  using normalized_contract
  by (simp add: lpc_reinterface_def lpc_attach_answers_def)
qed


theorem lpp_observer_output_arithmetic_node_contract:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest={}"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_observed_functor_link T fs fuel P Q nds states contexts Fs functor_contexts
   (nds!i) (Fs!i) (states!i) (contexts!i) (functor_contexts!i) a e gs helper_payload helper_saved result_var middle"
 and source_shape: "states!i=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),helper_payload)#helper_saved"
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
   lpp_observer_output_invariant leaf_set specs rest oi hi ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser value_name) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved) \<Longrightarrow> node_conditions (lpcl_target middle) rho"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature
   (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
   node_conditions (lpp_observer_output_invariant leaf_set specs rest oi hi) rest returned i"
proof (rule lpp_observer_canonical_node_contract[OF program clear])
 show "\<And>swaps runtime. lpp_observer_output_invariant leaf_set specs rest oi hi runtime \<Longrightarrow>
   lpp_observer_output_invariant leaf_set specs rest oi hi (lpc_return_scope_word swaps runtime)"
  by (simp add: lpp_observer_output_invariant_scopes[OF clear])
next
 fix eta runtime
 show "node_conditions i eta \<longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<longrightarrow>
   lpc_free_knowledge (set (Fs!i)) eta \<longrightarrow>
   lpp_stable_context_holds operation SP (contexts!i) eta \<longrightarrow>
   list_all (lpp_functor_fact_holds names eta) (functor_contexts!i) \<longrightarrow>
   lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta (states!i) \<longrightarrow>
   lpp_observer_output_invariant leaf_set specs rest oi hi runtime \<longrightarrow>
   SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]} \<longrightarrow>
   (\<forall>child u. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<longrightarrow>
    lpp_observer_output_invariant leaf_set specs rest oi hi child \<longrightarrow>
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
  and invariant: "lpp_observer_output_invariant leaf_set specs rest oi hi runtime"
  and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  and lower: "\<forall>child u. ([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+ \<longrightarrow>
    lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
     node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<longrightarrow>
    lpp_observer_output_invariant leaf_set specs rest oi hi child \<longrightarrow>
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
  show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime))
    (lp_ild Q) [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] returned"
  proof (rule lpp_checked_conditioned_is_output_contract[
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
   lpp_observer_output_invariant leaf_set specs rest oi hi ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser value_name) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved) \<Longrightarrow> node_conditions (lpcl_target middle) rho"
    by (rule target_init[OF conditions])
  next
   fix child u
   assume strict: "([(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))],u)\<in>(lp_ild Q)\<^sup>+"
   and module: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u"
   and child_invariant: "lpp_observer_output_invariant leaf_set specs rest oi hi child"
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
val checked = @{thms lpp_checked_conditioned_is_output_contract lpp_observer_output_arithmetic_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted output arithmetic node" else ();
\<close>
end
