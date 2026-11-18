theory LP_Prolog_Observer_Arithmetic_Normalization
 imports LP_Prolog_Observer_Checked_Control
begin

text \<open>Expose the existing checked arithmetic normalization as a context
witness. The scalar result may be an integer or a binary64 value accepted by
the fixed source operation profile. No arithmetic result updates the separate
caller observation until actual equality execution applies its substitution.\<close>

lemma lpp_checked_is_normalization_witness:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_observed_functor_link T fs fuel P Q nds states contexts Fs functor_contexts nd F source_rows source_context source_functors a e gs helper_payload helper_saved result_var middle"
    and domain: "lpp_finite_source_domain ''2:is'' [lp_ieval a eta,lp_ieval e eta]"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and evaluated: "lpp_stable_scalar_evaluation operation (lp_ieval e eta) (LPIFun (LPCUser value_name) [])"
 shows "\<exists>rho.
   ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser value_name) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env helper_payload eta)#lpc_return_eval eta helper_saved)=lpc_return_eval rho (states!lpcl_target middle) \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],
     [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>(lp_ild Q)\<^sup>+ \<and>
   lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho \<and>
   lpc_free_knowledge (set (Fs!lpcl_target middle)) rho \<and>
   lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho \<and>
   list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle)"
proof -
 let ?C = "\<lambda>xs. \<exists>rho. xs=lpc_return_eval rho (states!lpcl_target middle) \<and>
   ([(lpcn_pred nd,map eta (lpcn_vars nd))],
     [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>(lp_ild Q)\<^sup>+ \<and>
   lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho \<and>
   lpc_free_knowledge (set (Fs!lpcl_target middle)) rho \<and>
   lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho \<and>
   list_all (lpp_functor_fact_holds names rho) (functor_contexts!lpcl_target middle)"
 have facts: "lpp_finite_source_domain ''2:is'' [lp_ieval a eta,lp_ieval e eta] \<and> (\<forall>f.
   lpp_stable_scalar_evaluation operation (lp_ieval e eta) (LPIFun (LPCUser f) []) \<longrightarrow>
   ?C ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env helper_payload eta)#lpc_return_eval eta helper_saved))"
  by (rule lpp_functor_observed_is_domain_context[where J="\<lambda>_. True" and C="?C",
    OF compatible program checked domain known free observed functors]) auto
 show ?thesis using facts evaluated by blast
qed


lemma lpp_checked_attached_is_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_observed_functor_link T fs fuel P Q nds states contexts Fs functor_contexts nd F source_rows source_context source_functors a e gs helper_payload helper_saved result_var middle"
    and domain: "lpp_finite_source_domain ''2:is'' [lp_ieval a eta,lp_ieval e eta]"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and functors: "list_all (lpp_functor_fact_holds names eta) source_functors"
 and runtime_shape: "runtime=(LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [lp_ieval a eta,lp_ieval e eta])#
    map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved"
 and represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime=lpc_return_eval eta source_rows"
 and invariant: "lpp_leaf_stack_invariant leaf_set specs (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)"
 and lower: "\<And>value_name rho.
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
   lpp_leaf_stack_invariant leaf_set specs (lpc_reinterface (\<lambda>env x. env (Inr x))
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser value_name) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved)) \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
    (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x))
     ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser value_name) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved))) R subject returned"
 shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain)
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime)) R subject returned"
proof -
 let ?T = "lpp_domain_answers P lpp_builtin_signature (lpp_univ_source_builtin names operation) lpp_univ_source_domain"
 let ?L = "\<lambda>env x. env (Inl x)"
 let ?R = "\<lambda>env x. env (Inr x)"
 let ?norm = "\<lambda>f. (LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),combined_env)#combined_saved"
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
  have caller_invariant: "lpp_leaf_stack_invariant leaf_set specs (lpc_reinterface ?R (?norm f))"
   using invariant by (simp add: runtime_shape lpc_reinterface_def lpp_leaf_stack_invariant_def)
  show ?thesis by (rule lower[OF evaluated helper_projection strict child_known child_free child_observed child_functors caller_invariant])
 qed
 show ?thesis
  unfolding runtime_shape
  apply (simp add: lpc_reinterface_def lpc_attach_answers_def)
  apply (rule lpp_univ_evaluation_domain_contract[OF domain])
  using normalized_contract
  by (simp add: lpc_reinterface_def lpc_attach_answers_def)
qed

ML \<open>
val checked = @{thms lpp_checked_is_normalization_witness lpp_checked_attached_is_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted arithmetic normalization witness" else ();
\<close>
end
