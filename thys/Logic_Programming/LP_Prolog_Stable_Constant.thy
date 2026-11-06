theory LP_Prolog_Stable_Constant
 imports LP_Prolog_Stable_Primitive_Domain LP_Prolog_Finite_Context_Constant
begin

theorem lpp_stable_context_constant_contract:
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
      lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
        (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
  shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    (lpc_return_eval eta ss) R t ret"
proof -
  let ?n = "lpp_expression_value evidence (\<lambda>_. 0)"
  let ?synthetic = "((LPCGoals (LPCUnify a (lpp_integer_term ?n)#gs),active)#saved)"
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
    and expr: "e=lpp_expression_term evidence" and typed: "lpp_expression_check [] evidence"
    and swaps: "lpcl_swaps middle=[]"
    and link: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd ?synthetic
      (lpcn_ground nd) (lpcn_guards nd) [] F
      (lpp_add_evaluation_observation e (lpp_integer_term ?n) source_context) middle"
    using checked by (auto simp: lpp_check_finite_context_constant_def)
  have evaluated: "lpp_integer_evaluation (lp_ieval e eta) ?n"
    unfolding expr by (rule lpp_expression_evaluation[OF typed]) simp
  have evaluation: "lpp_stable_scalar_evaluation operation (lp_ieval e eta) (lp_ieval (lpp_integer_term ?n) eta)"
    using lpp_integer_evaluation_stable[OF compatible evaluated] by simp
  have facts: "lpp_stable_context_holds operation SP (lpp_add_evaluation_observation e (lpp_integer_term ?n) source_context) eta"
    by (rule lpp_stable_add_evaluation_context[OF observed evaluation])
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  have parent: "map eta (lpcn_vars nd)=map eta (lpcn_vars nd)" by simp
  obtain rho where same: "lpc_return_eval eta ?synthetic=lpc_return_eval rho (states!lpcl_target middle)"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
    and child_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
    and child_context: "lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
      [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>lp_ild Q"
    using lpp_stable_link_witness[OF compatible program link equations parent known free facts] by (simp add: swaps) blast
  have frame_same: "map snd (lpc_return_eval eta ?synthetic)=map snd (lpc_return_eval eta ss)"
    by (simp add: shape lpc_return_eval_def)
  have child_invariant: "J (lpc_return_eval rho (states!lpcl_target middle))"
    using frames[OF frame_same invariant] same by simp
  have child: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
    by (rule lower[OF r_into_trancl[OF edge] knowledge child_free child_context child_invariant])
  have normalized: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    ((LPCGoals (LPCUnify (lp_ieval a eta) (lpp_integer_value ?n)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) R t ret"
    using child same by (simp add: lpc_return_eval_def)
  have ground: "lp_seg_ground (lp_ieval e eta)"
    by (rule lpp_integer_evaluation_ground[OF evaluated])
  have exact: "lpp_stable_scalar_evaluation operation (lp_ieval e eta) v \<longleftrightarrow> v=lpp_integer_value ?n" for v
    by (rule lpp_stable_evaluation_integer_exact[OF compatible evaluated])
  have contracts: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) R t ret"
    if "lpp_stable_scalar_evaluation operation (lp_ieval e eta) (LPIFun (LPCUser f) [])" for f
    using normalized that exact by simp
  show ?thesis using lpp_stable_evaluation_normalized_contract[OF ground contracts]
    by (simp add: shape lpc_return_eval_def)
qed
ML \<open>
val checked = [@{thm lpp_stable_context_constant_contract}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable constant dependency" else ();
\<close>
end
