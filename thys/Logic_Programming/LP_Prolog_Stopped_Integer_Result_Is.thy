theory LP_Prolog_Stopped_Integer_Result_Is
 imports LP_Prolog_Stopped_Observed_Is LP_Prolog_Stable_Return_Receipts LP_Prolog_Stable_Integer_Result_Domain
begin

text \<open>The existing normalized evaluation/unification step is retained.
The extra fact describes only its successful result, and is introduced before
shared unification. No input literal type or successful return is assumed.\<close>

definition lpp_check_integer_result_is where
  "lpp_check_integer_result_is domain_receipt T fs fuel P Q nds states contexts Fs nd F ss source_context a e gs active saved result_var middle =
    (lpp_check_integer_result_receipt [] domain_receipt \<and> e=lpp_integer_result_term domain_receipt \<and>
     ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved \<and>
     vars_term e \<subseteq> set (lpcn_ground nd) \<union> lpp_source_context_ground source_context \<and>
     lpp_fresh_return result_var ss \<and> lpp_context_fresh result_var source_context \<and>
     result_var\<notin>set F \<and> result_var\<notin>set (lpcn_vars nd) \<and> list_all (lpp_fresh_guard result_var) (lpcn_guards nd) \<and>
     lpcl_swaps middle=[] \<and>
     lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd
       ((LPCGoals (LPCUnify a (Var result_var)#gs),active)#saved)
       (result_var#lpcn_ground nd) (lpcn_guards nd) [] F
       (lpp_context_add_integers (lpp_add_evaluation_observation e (Var result_var) source_context) [result_var]) middle)"

theorem lpp_integer_result_is_context:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_integer_result_is domain_receipt T fs fuel P Q nds states contexts Fs nd F ss source_context a e gs active saved result_var middle"
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
      C (lpc_return_eval rho (states!lpcl_target middle))"
  shows "lp_seg_ground (lp_ieval e eta) \<and> (\<forall>f.
    lpp_stable_scalar_evaluation operation (lp_ieval e eta) (LPIFun (LPCUser f) []) \<longrightarrow>
    C ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved))"
proof -
  have domain_check: "lpp_check_integer_result_receipt [] domain_receipt"
    and domain_term: "e=lpp_integer_result_term domain_receipt"
    using checked by (auto simp: lpp_check_integer_result_is_def)
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
    and expr_ground: "vars_term e \<subseteq> set (lpcn_ground nd) \<union> lpp_source_context_ground source_context"
    and result_var: "lpp_fresh_return result_var ss"
    and context_fresh: "lpp_context_fresh result_var source_context"
    and free_fresh: "result_var\<notin>set F"
    and interface: "result_var\<notin>set (lpcn_vars nd)"
    and guards: "list_all (lpp_fresh_guard result_var) (lpcn_guards nd)"
    and swaps: "lpcl_swaps middle=[]"
    and link: "lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd
      ((LPCGoals (LPCUnify a (Var result_var)#gs),active)#saved)
      (result_var#lpcn_ground nd) (lpcn_guards nd) [] F
      (lpp_context_add_integers (lpp_add_evaluation_observation e (Var result_var) source_context) [result_var]) middle"
    using checked by (auto simp: lpp_check_integer_result_is_def)
  have prior: "lpp_evaluation_context_holds (lpp_stable_scalar_evaluation operation) SP source_context eta"
    using observed by (simp add: lpp_stable_context_holds_def)
  have context_ground: "\<forall>x\<in>lpp_source_context_ground source_context. lp_seg_ground (eta x)"
    by (rule lpp_evaluation_context_ground_sound[where E="lpp_stable_scalar_evaluation operation", OF _ prior])
      (auto dest: lpp_stable_scalar_evaluation_ground)
  have ground: "lp_seg_ground (lp_ieval e eta)"
    using known expr_ground context_ground by (auto simp: lp_cut_knowledge_def lp_seg_ground_eval)
  have contracts: "C
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved)"
    if evaluated: "lpp_stable_scalar_evaluation operation (lp_ieval e eta) (LPIFun (LPCUser f) [])" for f
  proof -
  let ?nu = "eta(result_var:=(LPIFun (LPCUser f) []))"
  let ?synthetic = "((LPCGoals (LPCUnify a (Var result_var)#gs),active)#saved)"
  have fa: "result_var\<notin>vars_term a" and fe: "result_var\<notin>vars_term e"
    and rest: "lpp_fresh_return result_var ((LPCGoals gs,active)#saved)"
    using result_var by (auto simp: shape lpp_fresh_return_def)
  have unchanged: "lpc_return_eval ?nu ((LPCGoals gs,active)#saved)=lpc_return_eval eta ((LPCGoals gs,active)#saved)"
    by (rule lpp_fresh_return_eval[OF rest])
  have represented: "lpc_return_eval ?nu ?synthetic =
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved)"
    using unchanged lpp_fresh_term_eval[OF fa, of eta "LPIFun (LPCUser f) []"]
    by (simp add: lpc_return_eval_def)
  have extended: "lp_cut_knowledge (set (result_var#lpcn_ground nd)) (lpcn_guards nd) ?nu"
    using known guards lpp_fresh_guard_eval[of result_var _ eta "LPIFun (LPCUser f) []"]
      by (auto simp: lp_cut_knowledge_def list_all_iff intro: lp_seg_ground.intros)
  have parent: "map ?nu (lpcn_vars nd)=map eta (lpcn_vars nd)"
    using interface by (auto intro!: map_cong)
  have old_context: "lpp_stable_context_holds operation SP source_context ?nu"
    using lpp_stable_context_fresh_eval[OF context_fresh, of operation SP eta "LPIFun (LPCUser f) []"] observed by simp
  have evaluation: "lpp_stable_scalar_evaluation operation (lp_ieval e ?nu) (lp_ieval (Var result_var) ?nu)"
    using evaluated by (simp add: lpp_fresh_term_eval[OF fe])
  have facts: "lpp_stable_context_holds operation SP (lpp_add_evaluation_observation e (Var result_var) source_context) ?nu"
    by (rule lpp_stable_add_evaluation_context[OF old_context evaluation])
  have result_integer: "lpp_is_integer (?nu result_var)"
    using lpp_checked_actual_integer_result[OF compatible domain_check, of eta "LPIFun (LPCUser f) []"] evaluated domain_term
      by (simp add: lpp_integer_known_def)
  have result_known: "lpp_integer_known [result_var] ?nu"
    using result_integer by (auto simp: lpp_integer_known_def lpp_is_integer_def)
  have typed_facts: "lpp_stable_context_holds operation SP
      (lpp_context_add_integers (lpp_add_evaluation_observation e (Var result_var) source_context) [result_var]) ?nu"
    by (rule lpp_stable_add_integers_sound[OF facts result_known])
  have extended_free: "lpc_free_knowledge (set F) ?nu"
    using free free_fresh by (auto simp: lpc_free_knowledge_def inj_on_def)
  have equations: "lp_equations [] ?nu" by (simp add: lp_equations_def)
  obtain rho where same: "lpc_return_eval ?nu ?synthetic=lpc_return_eval rho (states!lpcl_target middle)"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
    and child_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
    and child_context: "lpp_stable_context_holds operation SP (contexts!lpcl_target middle) rho"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
      [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>lp_ild Q"
    using lpp_stable_link_witness[OF compatible program link equations parent extended extended_free typed_facts] by (simp add: swaps) blast
  have frame_same: "map snd (lpc_return_eval ?nu ?synthetic)=map snd (lpc_return_eval eta ss)"
    using arg_cong[OF unchanged, of "map snd"]
    by (simp add: shape lpc_return_eval_def)
  have child_invariant: "J (lpc_return_eval rho (states!lpcl_target middle))"
    using frames[OF frame_same invariant] same by simp
  have child: "C
    (lpc_return_eval rho (states!lpcl_target middle))"
    by (rule lower[OF r_into_trancl[OF edge] knowledge child_free child_context child_invariant])
  show "C
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved)"
    using child same represented by simp
  qed
  show ?thesis using ground contracts by blast
qed

theorem lpp_stopped_integer_result_is_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_integer_result_is domain_receipt T fs fuel P Q nds states contexts Fs nd F ss source_context a e gs active saved result_var middle"
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
    by (rule lpp_integer_result_is_context[where C="(\<lambda>xs. lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)) xs R t ret)" and J=J,
      OF compatible program checked known free observed invariant]) (fact frames, fact lower)
  have ground: "lp_seg_ground (lp_ieval e eta)" using facts by blast
  have contracts: "lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature))
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) R t ret"
    if "lpp_stable_scalar_evaluation operation (lp_ieval e eta) (LPIFun (LPCUser f) [])" for f
    using facts that by blast
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
    using checked by (auto simp: lpp_check_integer_result_is_def)
  show ?thesis using lpp_stopped_evaluation_normalized_contract[OF ground contracts]
    by (simp add: shape lpc_return_eval_def)
qed

ML \<open>
val checked = @{thms lpp_integer_result_is_context lpp_stopped_integer_result_is_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted checked integer-result step" else ();
\<close>
end
