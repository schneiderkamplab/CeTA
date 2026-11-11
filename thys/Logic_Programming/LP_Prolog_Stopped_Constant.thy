theory LP_Prolog_Stopped_Constant
  imports LP_Prolog_Stopped_Normalization LP_Prolog_Stable_Constant
begin

theorem lpp_stopped_context_constant_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_finite_context_constant T fs fuel P Q nds states contexts Fs nd F ss source_context evidence a e gs active saved middle"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_stable_context_holds operation SP source_context eta"
    and invariant: "J (lpc_return_eval eta ss)"
    and frames: "\<And>xs ys. map snd xs=map snd ys \<Longrightarrow> J ys \<Longrightarrow> J xs"
    and lower: "\<And>rho. ([(lpcn_pred nd,map eta (lpcn_vars nd))],
        [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho \<Longrightarrow>
      lpc_free_knowledge (set (Fs!lpcl_target middle)) rho \<Longrightarrow>
      lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho \<Longrightarrow>
      J (lpc_return_eval rho (states!lpcl_target middle)) \<Longrightarrow>
      lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature))
        (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
  shows "lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature))
    (lpc_return_eval eta ss) R t ret"
proof -
  have facts: "lp_seg_ground (lp_ieval e eta) \<and> (\<forall>f.
    lpp_stable_scalar_evaluation operation (lp_ieval e eta) (LPIFun (LPCUser f) []) \<longrightarrow>
    (\<lambda>xs. lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)) xs R t ret) ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved))"
    by (rule lpp_stable_context_constant_context[where C="(\<lambda>xs. lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)) xs R t ret)" and J=J,
      OF compatible program checked known free observed invariant]) (fact frames, fact lower)
  have ground: "lp_seg_ground (lp_ieval e eta)" using facts by blast
  have contracts: "lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature))
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) R t ret"
    if "lpp_stable_scalar_evaluation operation (lp_ieval e eta) (LPIFun (LPCUser f) [])" for f
    using facts that by blast
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
    using checked by (auto simp: lpp_check_finite_context_constant_def)
  show ?thesis using lpp_stopped_evaluation_normalized_contract[OF ground contracts]
    by (simp add: shape lpc_return_eval_def)
qed

ML \<open>
val checked = [@{thm lpp_stopped_context_constant_contract}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stopped constant dependency" else ();
\<close>
end
