theory LP_Prolog_Context_Free_Is_Normalized
  imports LP_Prolog_Context_Free_Is_Staged LP_Prolog_Evaluation_Normalization
begin

text \<open>Ferrum records evaluation followed by shared unification. Both
control edges represent one source is/2 operation; the intermediate equality
state is not exposed as an already completed Prolog source step.\<close>
definition lpp_check_context_free_is_normalized where
  "lpp_check_context_free_is_normalized fuel P Q nds states contexts Fs nd F ss source_context K evidence a e gs active saved result_var middle =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved \<and>
     e=lpp_expression_term evidence \<and> lpp_expression_check K evidence \<and>
     lpp_fresh_return result_var ss \<and> lpp_context_fresh result_var source_context \<and>
     result_var\<notin>set F \<and> result_var\<notin>set (lpcn_vars nd) \<and> list_all (lpp_fresh_guard result_var) (lpcn_guards nd) \<and>
     lpcl_swaps middle=[] \<and>
     lpp_check_context_free_link fuel Q nds states contexts Fs nd
       ((LPCGoals (LPCUnify a (Var result_var)#gs),active)#saved)
       (result_var#lpcn_ground nd) (lpcn_guards nd) [] F
       (lpp_add_evaluation_observation e (Var result_var) source_context) middle)"

theorem lpp_context_free_is_normalized_contract:
  assumes checked: "lpp_check_context_free_is_normalized fuel P Q nds states contexts Fs nd F ss source_context K evidence a e gs active saved result_var middle"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_source_context_holds SP source_context eta"
    and integers: "lpp_integer_known K eta"
    and invariant: "J (lpc_return_eval eta ss)"
    and frames: "\<And>xs ys. map snd xs=map snd ys \<Longrightarrow> J ys \<Longrightarrow> J xs"
    and lower: "\<And>rho. ([(lpcn_pred nd,map eta (lpcn_vars nd))],
        [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho \<Longrightarrow>
      lpc_free_knowledge (set (Fs!lpcl_target middle)) rho \<Longrightarrow>
      lpp_source_context_holds SP (contexts!lpcl_target middle) rho \<Longrightarrow>
      J (lpc_return_eval rho (states!lpcl_target middle)) \<Longrightarrow>
      lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
        (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
  shows "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    (lpc_return_eval eta ss) R t ret"
proof -
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
    and expr: "e=lpp_expression_term evidence" and typed: "lpp_expression_check K evidence"
    and result_var: "lpp_fresh_return result_var ss"
    and context_fresh: "lpp_context_fresh result_var source_context"
    and free_fresh: "result_var\<notin>set F"
    and interface: "result_var\<notin>set (lpcn_vars nd)"
    and guards: "list_all (lpp_fresh_guard result_var) (lpcn_guards nd)"
    and swaps: "lpcl_swaps middle=[]"
    and link: "lpp_check_context_free_link fuel Q nds states contexts Fs nd
      ((LPCGoals (LPCUnify a (Var result_var)#gs),active)#saved)
      (result_var#lpcn_ground nd) (lpcn_guards nd) [] F
      (lpp_add_evaluation_observation e (Var result_var) source_context) middle"
    using checked by (auto simp: lpp_check_context_free_is_normalized_def)
  obtain n where evaluated: "lpp_integer_evaluation (lp_ieval e eta) n"
    using lpp_checked_expression_finishes[OF typed integers] expr by blast
  let ?nu = "eta(result_var:=lpp_integer_value n)"
  let ?synthetic = "((LPCGoals (LPCUnify a (Var result_var)#gs),active)#saved)"
  have fa: "result_var\<notin>vars_term a" and fe: "result_var\<notin>vars_term e"
    and rest: "lpp_fresh_return result_var ((LPCGoals gs,active)#saved)"
    using result_var by (auto simp: shape lpp_fresh_return_def)
  have unchanged: "lpc_return_eval ?nu ((LPCGoals gs,active)#saved)=lpc_return_eval eta ((LPCGoals gs,active)#saved)"
    by (rule lpp_fresh_return_eval[OF rest])
  have represented: "lpc_return_eval ?nu ?synthetic =
    ((LPCGoals (LPCUnify (lp_ieval a eta) (lpp_integer_value n)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved)"
    using unchanged lpp_fresh_term_eval[OF fa, of eta "lpp_integer_value n"]
    by (simp add: lpc_return_eval_def)
  have extended: "lp_cut_knowledge (set (result_var#lpcn_ground nd)) (lpcn_guards nd) ?nu"
    by (rule lpp_fresh_integer_knowledge[OF known guards])
  have parent: "map ?nu (lpcn_vars nd)=map eta (lpcn_vars nd)"
    using interface by (auto intro!: map_cong)
  have old_context: "lpp_source_context_holds SP source_context ?nu"
    using lpp_context_fresh_eval[OF context_fresh, of SP eta "lpp_integer_value n"] observed by simp
  have evaluation: "lpp_integer_result (lp_ieval e ?nu) (lp_ieval (Var result_var) ?nu)"
    using evaluated by (simp add: lpp_fresh_term_eval[OF fe] lpp_integer_result_def)
  have facts: "lpp_source_context_holds SP (lpp_add_evaluation_observation e (Var result_var) source_context) ?nu"
    by (rule lpp_add_evaluation_observation_holds[OF old_context evaluation])
  have extended_free: "lpc_free_knowledge (set F) ?nu"
    using free free_fresh by (auto simp: lpc_free_knowledge_def inj_on_def)
  have equations: "lp_equations [] ?nu" by (simp add: lp_equations_def)
  obtain rho where same: "lpc_return_eval ?nu ?synthetic=lpc_return_eval rho (states!lpcl_target middle)"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
    and child_free: "lpc_free_knowledge (set (Fs!lpcl_target middle)) rho"
    and child_context: "lpp_source_context_holds SP (contexts!lpcl_target middle) rho"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
      [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>lp_ild Q"
    using lpp_context_free_link_witness[OF link equations parent extended extended_free facts] by (simp add: swaps) blast
  have frame_same: "map snd (lpc_return_eval ?nu ?synthetic)=map snd (lpc_return_eval eta ss)"
    using arg_cong[OF unchanged, of "map snd"]
    by (simp add: shape lpc_return_eval_def)
  have child_invariant: "J (lpc_return_eval rho (states!lpcl_target middle))"
    using frames[OF frame_same invariant] same by simp
  have child: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    (lpc_return_eval rho (states!lpcl_target middle)) R t ret"
    by (rule lower[OF r_into_trancl[OF edge] knowledge child_free child_context child_invariant])
  have normalized: "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    ((LPCGoals (LPCUnify (lp_ieval a eta) (lpp_integer_value n)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) R t ret"
    using child same represented by simp
  show ?thesis using lpp_integer_evaluation_normalized_contract[OF evaluated normalized]
    by (simp add: shape lpc_return_eval_def)
qed
end
