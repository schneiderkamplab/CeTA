theory LP_Prolog_Observer_Univ_Contract
 imports LP_Prolog_Observer_Univ_Witness
begin

definition lpp_observer_univ_normalized where
 "lpp_observer_univ_normalized names f ts requested pending env saved =
  (LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
   LPCUnify requested (lpp_argument_list (LPIFun (names f) []#ts))#pending),env)#saved"

lemma lpp_checked_attached_univ_contract:
 fixes SP :: "string lpp_success_clause list"
 assumes compatible: "lpp_stable_integer_operations operation"
 and program: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_univ_evaluation_context T fs fuel Q nds states contexts functor_contexts Fs nd F ss source_context source_functors
    input_template requested gs active saved value_variable name_variable arguments_variable middle"
 and separation_bound: "lpcl_target middle<length separation_contexts"
 and separation_transport: "lpp_check_separation_transport initialized_separation
   (separation_contexts!lpcl_target middle) (lp_cut_instance_subst (lpcl_bindings middle))"
 and separation_initialized: "\<And>f ts. lp_ieval input_template eta=LPIFun f ts \<Longrightarrow>
   list_all (lpp_separation_holds
     (eta(value_variable:=LPIFun f ts,name_variable:=LPIFun (names f) [],arguments_variable:=lpp_argument_list ts)))
     initialized_separation"
 and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
 and free: "lpc_free_knowledge (set F) eta"
 and context_held: "lpp_stable_context_holds operation SP source_context eta"
 and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and selected: "(''2:=..'',2)\<in>B"
 and domain: "\<And>a b. lpp_univ_view_domain a b \<Longrightarrow> D ''2:=..'' [a,b]"
 and coverage: "\<And>a b out. lpp_univ_view_domain a b \<Longrightarrow> U ''2:=..'' [a,b] out \<Longrightarrow>
    lpp_univ_view_outcome names a b out"
 and runtime_shape: "runtime=(LPCGoals (LPCAtom (LPIFun (LPCUser ''2:=..'') [lp_ieval input_template eta,lp_ieval requested eta])#
   map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta ss"
 and invariant: "lpp_leaf_stack_invariant leaf_set specs (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
 and lower: "\<And>f ts rho. lp_ieval input_template eta=LPIFun f ts \<Longrightarrow>
   lpc_reinterface (\<lambda>env x. env (Inl x)) (lpp_observer_univ_normalized names f ts (lp_ieval requested eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) combined_env combined_saved)=lpc_return_eval rho (states!lpcl_target middle) \<Longrightarrow>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],
     [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>lp_ild Q \<Longrightarrow>
   lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho \<Longrightarrow>
   lpc_free_knowledge (set (Fs!lpcl_target middle)) rho \<Longrightarrow>
   lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho \<Longrightarrow>
   list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle) \<Longrightarrow>
   lpp_separation_node_conditions separation_contexts (lpcl_target middle) rho \<Longrightarrow>
   lpp_leaf_stack_invariant leaf_set specs (lpc_reinterface (\<lambda>env x. env (Inr x)) (lpp_observer_univ_normalized names f ts (lp_ieval requested eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) combined_env combined_saved)) \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) (lpp_observer_univ_normalized names f ts (lp_ieval requested eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) combined_env combined_saved))) R subject returned"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) R subject returned"
proof -
 let ?T = "lpp_domain_answers P B U D"
 let ?L = "\<lambda>env x. env (Inl x)"
 let ?R = "\<lambda>env x. env (Inr x)"
 let ?norm = "\<lambda>f ts. lpp_observer_univ_normalized names f ts (lp_ieval requested eta) (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) combined_env combined_saved"
 have source_shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:=..'') [input_template,requested])#gs),active)#saved"
 and dom_check: "lpp_check_univ_view_domain F input_template requested"
  using checked by (auto simp: lpp_check_univ_evaluation_context_def)
 have admitted: "lpp_univ_view_domain (lp_ieval input_template eta) (lp_ieval requested eta)"
  by (rule lpp_check_univ_view_domain_sound[OF dom_check free])
 have interfaces: "?L combined_env=lpc_return_env active eta"
   "lpc_reinterface ?L combined_saved=lpc_return_eval eta saved"
  using represented by (auto simp: runtime_shape source_shape lpc_reinterface_def lpc_return_eval_def)
 have normalized_contract: "lp_answer_contract ?T (lpc_attach_answers rest (lpc_reinterface ?R (?norm f ts))) R subject returned"
  if input: "lp_ieval input_template eta=LPIFun f ts" for f ts
 proof -
  obtain rho where same: "((LPCGoals (LPCUnify (LPIFun f ts) (LPIFun f ts)#
     LPCUnify (lp_ieval requested eta) (lpp_argument_list (LPIFun (names f) [] # ts))#
     map (lp_cut_map (\<lambda>u. lp_ieval u eta)) gs),lpc_return_env active eta)#lpc_return_eval eta saved)=lpc_return_eval rho (states!lpcl_target middle)"
  and strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
     [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>lp_ild Q"
  and child_known: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
  and child_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
  and child_observed: "lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho"
  and child_functors: "list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle)"
  and child_separation: "lpp_separation_node_conditions separation_contexts (lpcl_target middle) rho"
   using lpp_checked_univ_normalization_witness[OF compatible program checked separation_bound separation_transport
     separation_initialized known free context_held functors input] by blast
  have helper_projection: "lpc_reinterface ?L (?norm f ts)=lpc_return_eval rho (states!lpcl_target middle)"
   using same interfaces by (simp add: lpc_reinterface_def lpp_observer_univ_normalized_def)
  have caller_invariant: "lpp_leaf_stack_invariant leaf_set specs (lpc_reinterface ?R (?norm f ts))"
   using invariant by (simp add: runtime_shape lpc_reinterface_def lpp_leaf_stack_invariant_def lpp_observer_univ_normalized_def)
  show ?thesis by (rule lower[OF input helper_projection strict child_known child_free child_observed child_functors child_separation caller_invariant])
 qed
 have contracts: "lp_answer_contract ?T
   ((LPCGoals (LPCUnify (lp_ieval requested eta) (lpp_argument_list (LPIFun (names f) []#ts))#
     (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs @ map (lp_cut_map (\<lambda>t. lp_ieval t (?R combined_env))) rest)),?R combined_env)#
       lpc_attach_answers rest (lpc_reinterface ?R combined_saved)) R subject returned"
  if input: "lp_ieval input_template eta=LPIFun f ts" for f ts
  by (rule lpp_reflexive_equality_contract_drop)
   (use normalized_contract[OF input] in \<open>simp add: lpp_observer_univ_normalized_def lpc_reinterface_def lpc_attach_answers_def\<close>)
 show ?thesis
  unfolding runtime_shape
  apply (simp add: lpc_reinterface_def lpc_attach_answers_def)
  apply (rule lpp_univ_view_normalized_contract[where names=names and input_value="lp_ieval input_template eta" and requested="lp_ieval requested eta" and B=B and U=U and D=D, OF selected coverage[OF admitted] domain[OF admitted]])
  apply assumption
  subgoal for f ts using contracts[of f ts]
   by (simp add: lpc_reinterface_def lpc_attach_answers_def)
  done
qed

ML \<open>
val checked = @{thms lpp_checked_attached_univ_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted attached univ contract" else ();
\<close>
end
