theory LP_Prolog_Observer_Is_Contract
 imports LP_Prolog_Observer_Arithmetic_Normalization LP_Prolog_Observer_Frontier_Term_Test_Node
begin

text \<open>Arithmetic normalization preserves the actual joint environments.
The existing scalar semantics covers both integer and binary64 evaluation;
finite execution supplies the domain premise. The normalized equality needs
its own represented child and return contract.\<close>

lemma lpp_observer_is_normalized_invariant:
 assumes shape: "runtime=(LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),env)#saved"
 and invariant: "lpp_observer_invariant A specs rest runtime"
 shows "lpp_observer_invariant A specs rest
   ((LPCGoals (LPCUnify a (LPIFun (LPCUser value_name) [])#gs),env)#saved)"
 using invariant
 by (auto simp: shape lpp_observer_invariant_def lpp_leaf_stack_invariant_def
  lpc_reinterface_def lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)

lemma lpp_observer_is_finite_domain:
 assumes shape: "runtime=(LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,e])#gs),env)#saved"
 and invariant: "lpp_observer_invariant A specs rest runtime"
 shows "lpp_finite_source_domain ''2:is'' [a,e]"
proof (rule lpp_finite_is_source_domain)
 show "lpp_finite_term e" using invariant
 by (auto simp: shape lpp_observer_invariant_def lpc_reinterface_def
  lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)
qed

lemma lpp_checked_observer_is_contract:
 fixes SP :: "string lpp_success_clause list"
 and combined_env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes compatible: "lpp_stable_integer_operations operation"
 and program: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_observed_functor_link T fs fuel P Q nds states contexts Fs functor_contexts nd F source_rows source_context source_functors a e gs helper_payload helper_saved result_var middle"
 and bounds: "lpcl_target middle<length nds" "lpcl_target middle<length states"
   "lpcl_target middle<length contexts" "lpcl_target middle<length Fs"
   "lpcl_target middle<length functor_contexts"
 and child_conditions: "\<And>rho. node_conditions (lpcl_target middle) rho"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and free: "lpc_free_knowledge (set F) eta"
 and observed: "lpp_stable_context_holds operation SP source_context eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and shape: "runtime=(LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [lp_ieval a eta,lp_ieval e eta])#
    map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta source_rows"
 and invariant: "lpp_observer_invariant leaf_set specs rest runtime"
 and lower: "\<And>child u. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
   lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) child) u \<Longrightarrow>
   lpp_observer_invariant leaf_set specs rest child \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child)) (lp_ild Q) u returned"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] returned"
proof -
 have domain: "lpp_finite_source_domain ''2:is'' [lp_ieval a eta,lp_ieval e eta]"
  by (rule lpp_observer_is_finite_domain[OF shape invariant])
 have leaf: "lpp_leaf_stack_invariant leaf_set specs (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
  using invariant by (simp add: lpp_observer_invariant_def)
 show ?thesis
 proof (rule lpp_checked_attached_is_contract[OF compatible program checked domain known free observed functors shape represented leaf])
  fix value_name
  fix rho :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  let ?child = "(LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser value_name) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved"
  let ?u = "[(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))]"
  assume evaluated: "lpp_stable_scalar_evaluation operation (lp_ieval e eta) (LPIFun (LPCUser value_name) [])"
   and same: "lpc_reinterface (\<lambda>env x. env (Inl x)) ?child=lpc_return_eval rho (states!lpcl_target middle)"
   and strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],?u)\<in>(lp_ild Q)\<^sup>+"
   and child_known: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
   and child_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
   and child_observed: "lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho"
   and child_functors: "list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle)"
   and child_leaf: "lpp_leaf_stack_invariant leaf_set specs (lpc_reinterface (\<lambda>env x. env (Inr x)) ?child)"
  have rep: "lpp_premised_functor_module_rep names operation SP nds states contexts Fs functor_contexts
    node_conditions (lpc_reinterface (\<lambda>env x. env (Inl x)) ?child) ?u"
   unfolding same
   by (rule lpp_premised_functor_module_intro[where node_conditions=node_conditions, OF bounds child_known child_free child_observed child_conditions child_functors])
  have inv: "lpp_observer_invariant leaf_set specs rest ?child"
   by (rule lpp_observer_is_normalized_invariant[OF shape invariant])
  show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) ?child)) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] returned"
   by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] lower[OF strict rep inv]])
 qed
qed

end
