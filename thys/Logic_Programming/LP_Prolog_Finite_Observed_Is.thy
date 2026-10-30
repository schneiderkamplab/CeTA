theory LP_Prolog_Finite_Observed_Is
  imports LP_Prolog_Finite_Context_Is LP_Prolog_Evaluation_Comparison
begin

text \<open>Ferrum records evaluation followed by shared unification. Both
control edges represent one source is/2 operation; the intermediate equality
state is not exposed as an already completed Prolog source step.\<close>
definition lpp_check_finite_observed_is where
  "lpp_check_finite_observed_is T fs fuel P Q nds states contexts Fs nd F ss source_context a e gs active saved result_var middle =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved \<and>
     vars_term e \<subseteq> set (lpcn_ground nd) \<union> lpp_source_context_ground source_context \<and>
     lpp_fresh_return result_var ss \<and> lpp_context_fresh result_var source_context \<and>
     result_var\<notin>set F \<and> result_var\<notin>set (lpcn_vars nd) \<and> list_all (lpp_fresh_guard result_var) (lpcn_guards nd) \<and>
     lpcl_swaps middle=[] \<and>
     lpp_check_evaluation_link T fs fuel Q nds states contexts Fs nd
       ((LPCGoals (LPCUnify a (Var result_var)#gs),active)#saved)
       (result_var#lpcn_ground nd) (lpcn_guards nd) [] F
       (lpp_add_evaluation_observation e (Var result_var) source_context) middle)"

theorem lpp_finite_observed_is_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_finite_observed_is T fs fuel P Q nds states contexts Fs nd F ss source_context a e gs active saved result_var middle"
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
      (lpp_add_evaluation_observation e (Var result_var) source_context) middle"
    using checked by (auto simp: lpp_check_finite_observed_is_def)
  have ground: "lp_seg_ground (lp_ieval e eta)"
    using known expr_ground lpp_evaluation_context_ground_sound[OF lpp_finite_evaluation_ground observed]
    by (auto simp: lp_cut_knowledge_def lp_seg_ground_eval)
  have contracts: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_finite_source_builtin lpp_finite_source_domain)
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) R t ret"
    if evaluated: "lpp_finite_evaluation_result (lp_ieval e eta) (LPIFun (LPCUser f) [])" for f
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
  have old_context: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP source_context ?nu"
    using lpp_evaluation_context_fresh_eval[OF context_fresh, of lpp_finite_evaluation_result SP eta "LPIFun (LPCUser f) []"] observed by simp
  have evaluation: "lpp_finite_evaluation_result (lp_ieval e ?nu) (lp_ieval (Var result_var) ?nu)"
    using evaluated by (simp add: lpp_fresh_term_eval[OF fe])
  have facts: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP (lpp_add_evaluation_observation e (Var result_var) source_context) ?nu"
    by (rule lpp_add_evaluation_context_holds[OF old_context evaluation])
  have extended_free: "lpc_free_knowledge (set F) ?nu"
    using free free_fresh by (auto simp: lpc_free_knowledge_def inj_on_def)
  have equations: "lp_equations [] ?nu" by (simp add: lp_equations_def)
  obtain rho where same: "lpc_return_eval ?nu ?synthetic=lpc_return_eval rho (states!lpcl_target middle)"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
    and child_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
    and child_context: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP (contexts!lpcl_target middle) rho"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
      [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>lp_ild Q"
    using lpp_evaluation_link_witness[OF lpp_finite_evaluation_integer_contract lpp_finite_evaluation_ground program link equations parent extended extended_free facts] by (simp add: swaps) blast
  have frame_same: "map snd (lpc_return_eval ?nu ?synthetic)=map snd (lpc_return_eval eta ss)"
    using arg_cong[OF unchanged, of "map snd"]
    by (simp add: shape lpc_return_eval_def)
  have child_invariant: "J (lpc_return_eval rho (states!lpcl_target middle))"
    using frames[OF frame_same invariant] same by simp
  have child: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_finite_source_builtin lpp_finite_source_domain)
    (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
    by (rule lower[OF r_into_trancl[OF edge] knowledge child_free child_context child_invariant])
  show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_finite_source_builtin lpp_finite_source_domain)
    ((LPCGoals (LPCUnify (lp_ieval a eta) (LPIFun (LPCUser f) [])#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) R t ret"
    using child same represented by simp
  qed
  show ?thesis using lpp_finite_evaluation_normalized_contract[OF ground contracts]
    by (simp add: shape lpc_return_eval_def)
qed

ML \<open>
val checked = [@{thm lpp_finite_observed_is_contract}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted finite evaluation source dependency" else ();
\<close>
end
