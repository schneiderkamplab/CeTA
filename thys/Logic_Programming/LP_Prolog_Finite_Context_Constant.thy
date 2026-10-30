theory LP_Prolog_Finite_Context_Constant
 imports LP_Prolog_Finite_Context_Is
begin

text \<open>A closed integer expression normalizes to shared unification with
its checked value. The equality receipt retains failure and saved alternatives.\<close>
definition lpp_check_finite_context_constant where
  "lpp_check_finite_context_constant T fs fuel P Q nds states contexts Fs nd F ss source_context evidence a e gs active saved middle =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved \<and>
     e=lpp_expression_term evidence \<and> lpp_expression_check [] evidence \<and>
     lpcl_swaps middle=[] \<and>
     lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd
       ((LPCGoals (LPCUnify a (lpp_integer_term (lpp_expression_value evidence (\<lambda>_. 0)))#gs),active)#saved)
       (lpcn_ground nd) (lpcn_guards nd) [] F
       (lpp_add_evaluation_observation e (lpp_integer_term (lpp_expression_value evidence (\<lambda>_. 0))) source_context) middle)"

theorem lpp_finite_context_constant_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_finite_context_constant T fs fuel P Q nds states contexts Fs nd F ss source_context evidence a e gs active saved middle"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP source_context eta"
    and invariant: "J (lpc_return_eval eta ss)"
    and frames: "\<And>xs ys. map snd xs=map snd ys \<Longrightarrow> J ys \<Longrightarrow> J xs"
    and lower: "\<And>rho. ([(lpcn_pred nd,map eta (lpcn_vars nd))],
        [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho \<Longrightarrow>
      lpc_free_knowledge (set (Fs!lpcl_target middle)) rho \<Longrightarrow>
      lpp_evaluation_context_holds lpp_finite_evaluation_result SP (contexts!lpcl_target middle) rho \<Longrightarrow>
      J (lpc_return_eval rho (states!lpcl_target middle)) \<Longrightarrow>
      lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_finite_source_builtin lpp_finite_source_domain)
        (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
  shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_finite_source_builtin lpp_finite_source_domain)
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
  have evaluation: "lpp_finite_evaluation_result (lp_ieval e eta) (lp_ieval (lpp_integer_term ?n) eta)"
    using evaluated by (simp add: lpp_finite_evaluation_integer[OF evaluated] lpp_integer_result_def)
  have facts: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP (lpp_add_evaluation_observation e (lpp_integer_term ?n) source_context) eta"
    by (rule lpp_add_evaluation_context_holds[OF observed evaluation])
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  have parent: "map eta (lpcn_vars nd)=map eta (lpcn_vars nd)" by simp
  obtain rho where same: "lpc_return_eval eta ?synthetic=lpc_return_eval rho (states!lpcl_target middle)"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
    and child_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
    and child_context: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP (contexts!lpcl_target middle) rho"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
      [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>lp_ild Q"
    using lpp_evaluation_link_witness[OF lpp_finite_evaluation_integer_contract lpp_finite_evaluation_ground program link equations parent known free facts] by (simp add: swaps) blast
  have frame_same: "map snd (lpc_return_eval eta ?synthetic)=map snd (lpc_return_eval eta ss)"
    by (simp add: shape lpc_return_eval_def)
  have child_invariant: "J (lpc_return_eval rho (states!lpcl_target middle))"
    using frames[OF frame_same invariant] same by simp
  have child: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_finite_source_builtin lpp_finite_source_domain)
    (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
    by (rule lower[OF r_into_trancl[OF edge] knowledge child_free child_context child_invariant])
  have normalized: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_finite_source_builtin lpp_finite_source_domain)
    ((LPCGoals (LPCUnify (lp_ieval a eta) (lpp_integer_value ?n)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) R t ret"
    using child same by (simp add: lpc_return_eval_def)
  have ground: "lp_seg_ground (lp_ieval e eta)"
    by (rule lpp_integer_evaluation_ground[OF evaluated])
  have exact: "lpp_finite_evaluation_result (lp_ieval e eta) v \<longleftrightarrow> v=lpp_integer_value ?n" for v
    unfolding expr by (rule lpp_finite_evaluation_exact[where K="[]" and rho="\<lambda>_. 0", OF typed]) simp
  have contracts: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_finite_source_builtin lpp_finite_source_domain)
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) R t ret"
    if "lpp_finite_evaluation_result (lp_ieval e eta) (LPIFun (LPCUser f) [])" for f
    using normalized that exact by simp
  show ?thesis using lpp_finite_evaluation_normalized_contract[OF ground contracts]
    by (simp add: shape lpc_return_eval_def)
qed
end
