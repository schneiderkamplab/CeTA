theory LP_Prolog_Finite_Direct_Observed_Is
 imports LP_Prolog_Finite_Direct_Invariant LP_Prolog_Stable_Observed_Is
begin

theorem lpp_finite_direct_observed_is_invariant_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_observed_evaluation_link T fs fuel P Q nds states contexts Fs nd F ss source_context a e gs active saved result_var middle"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and invariant: "lpp_finite_direct_invariant A (lpc_return_eval eta ss)"
    and extra: "K (lpc_return_eval eta ss)"
    and frames: "\<And>xs ys. map snd xs=map snd ys \<Longrightarrow> K ys \<Longrightarrow> K xs"
    and lower: "\<And>rho. ([(lpcn_pred nd,map eta (lpcn_vars nd))],
        [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho \<Longrightarrow>
      lpc_free_knowledge (set (Fs!lpcl_target middle)) rho \<Longrightarrow>
      lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho \<Longrightarrow>
      lpp_finite_direct_invariant A (lpc_return_eval rho (states!lpcl_target middle)) \<Longrightarrow>
      K (lpc_return_eval rho (states!lpcl_target middle)) \<Longrightarrow>
      lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
        (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
  shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    (lpc_return_eval eta ss) R t ret"
proof -
 have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
   using checked by (auto simp: lpp_check_observed_evaluation_link_def)
 have finite: "lpp_finite_term (lp_ieval e eta)"
   using invariant by (auto simp: shape lpc_return_eval_def
     lpp_finite_direct_invariant_def lpp_finite_direct_state_def)
 have domain: "lpp_finite_source_domain ''2:is'' [lp_ieval a eta,lp_ieval e eta]"
   by (rule lpp_finite_is_source_domain[OF finite])
 have normalized: "lpp_finite_direct_invariant A
     ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
       lpc_return_env active eta)#lpc_return_eval eta saved)"
   if inv: "lpp_finite_direct_invariant A (lpc_return_eval eta ss)" for f
   using lpp_finite_direct_is_normalization inv
   by (auto simp: shape lpc_return_eval_def)
 have extra_normalized: "K
     ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
       lpc_return_env active eta)#lpc_return_eval eta saved)" for f
   by (rule frames[OF _ extra]) (simp add: shape lpc_return_eval_def)
 show ?thesis
   by (rule lpp_stable_observed_is_domain_contract[where J="\<lambda>xs. lpp_finite_direct_invariant A xs \<and> K xs",
       OF compatible program checked domain known free observed])
     (use invariant extra normalized extra_normalized lower in auto)
qed

theorem lpp_finite_direct_observed_is_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_observed_evaluation_link T fs fuel P Q nds states contexts Fs nd F ss source_context a e gs active saved result_var middle"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and invariant: "lpp_finite_direct_invariant A (lpc_return_eval eta ss)"
    and lower: "\<And>rho. ([(lpcn_pred nd,map eta (lpcn_vars nd))],
        [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho \<Longrightarrow>
      lpc_free_knowledge (set (Fs!lpcl_target middle)) rho \<Longrightarrow>
      lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho \<Longrightarrow>
      lpp_finite_direct_invariant A (lpc_return_eval rho (states!lpcl_target middle)) \<Longrightarrow>
      lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
        (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
  shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    (lpc_return_eval eta ss) R t ret"
 by (rule lpp_finite_direct_observed_is_invariant_contract[where K="\<lambda>_. True",
       OF compatible program checked known free observed invariant])
    (use lower in auto)


lemma lpp_finite_large_arity_error_contract:
 assumes finite: "lpp_finite_term (LPIFun f ts)"
   and arity: "2<length ts"
 shows "lp_answer_contract
   (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
   ((LPCGoals (LPCAtom (LPIFun (LPCUser ''2:is'') [a,LPIFun f ts])#gs),eta)#saved) R t ret"
 by (rule lpp_stable_evaluation_domain_contract[OF lpp_finite_is_source_domain[OF finite]])
    (use arity in \<open>auto dest: lpp_stable_evaluation_arity\<close>)

ML \<open>
val checked = [@{thm lpp_finite_direct_observed_is_invariant_contract},
 @{thm lpp_finite_direct_observed_is_contract}, @{thm lpp_finite_large_arity_error_contract}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite direct observed evaluation" else ();
\<close>
end
