theory LP_Prolog_Context_Is_Constant
 imports LP_Prolog_Context_Is_Staged
begin

text \<open>A closed integer expression normalizes to shared unification with
its checked value. The equality receipt retains failure and saved alternatives.\<close>
definition lpp_check_context_is_constant where
  "lpp_check_context_is_constant fuel P Q nds states contexts nd ss source_context evidence a e gs active saved middle returned arity action =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved \<and>
     e=lpp_expression_term evidence \<and> lpp_expression_check [] evidence \<and>
     lpcl_swaps middle=[] \<and>
     lpp_check_context_table_link fuel Q nds states contexts nd
       ((LPCGoals (LPCUnify a (lpp_integer_term (lpp_expression_value evidence (\<lambda>_. 0)))#gs),active)#saved)
       (lpcn_ground nd) (lpcn_guards nd) []
       (lpp_add_evaluation_observation e (lpp_integer_term (lpp_expression_value evidence (\<lambda>_. 0))) source_context) middle \<and>
     lpp_check_context_cut_action fuel P Q nds states contexts (nds!lpcl_target middle)
       (states!lpcl_target middle) (contexts!lpcl_target middle) returned arity action)"

theorem lpp_context_is_constant_sound:
  assumes checked: "lpp_check_context_is_constant fuel P Q nds states contexts nd ss source_context evidence a e gs active saved middle returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and observed: "lpp_source_context_holds SP source_context eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps tt) u)"
proof -
  let ?n = "lpp_expression_value evidence (\<lambda>_. 0)"
  let ?synthetic = "((LPCGoals (LPCUnify a (lpp_integer_term ?n)#gs),active)#saved)"
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
    and expr: "e=lpp_expression_term evidence" and typed: "lpp_expression_check [] evidence"
    and swaps: "lpcl_swaps middle=[]"
    and link: "lpp_check_context_table_link fuel Q nds states contexts nd ?synthetic
      (lpcn_ground nd) (lpcn_guards nd) []
      (lpp_add_evaluation_observation e (lpp_integer_term ?n) source_context) middle"
    and action: "lpp_check_context_cut_action fuel P Q nds states contexts (nds!lpcl_target middle)
      (states!lpcl_target middle) (contexts!lpcl_target middle) returned arity action"
    using checked by (auto simp: lpp_check_context_is_constant_def)
  have evaluated: "lpp_integer_evaluation (lp_ieval e eta) ?n"
    unfolding expr by (rule lpp_expression_evaluation[OF typed]) simp
  have exact: "\<And>outcome. lpp_integer_source_builtin ''2:is'' [lp_ieval a eta,lp_ieval e eta] outcome =
    lpp_integer_is_outcome (lp_ieval a eta) (lp_ieval e eta) outcome" by simp
  have source: "lpc_answer_transition P
    ((LPCGoals (LPCUnify (lp_ieval a eta) (lpp_integer_value ?n)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) event tt"
    by (rule lpp_checked_is_uses_shared_equality[where U=lpp_integer_source_builtin, OF evaluated exact])
      (use step in \<open>simp add: shape lpc_return_eval_def\<close>)
  have actual: "lpc_answer_transition P (lpc_return_eval eta ?synthetic) event tt"
    using source by (simp add: lpc_return_eval_def)
  have silent: "event=None" using source by (cases rule: lpc_answer_transition.cases) auto
  have evaluation: "lpp_integer_result (lp_ieval e eta) (lp_ieval (lpp_integer_term ?n) eta)"
    using evaluated by (simp add: lpp_integer_result_def)
  have facts: "lpp_source_context_holds SP (lpp_add_evaluation_observation e (lpp_integer_term ?n) source_context) eta"
    by (rule lpp_add_evaluation_observation_holds[OF observed evaluation])
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  have parent: "map eta (lpcn_vars nd)=map eta (lpcn_vars nd)" by simp
  obtain rho where same: "lpc_return_eval eta ?synthetic=lpc_return_eval rho (states!lpcl_target middle)"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
    and child_context: "lpp_source_context_holds SP (contexts!lpcl_target middle) rho"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
      [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>lp_ild Q"
    using lpp_context_table_link_witness[OF link equations parent known facts] by (simp add: swaps) blast
  have child_step: "lpc_answer_transition P (lpc_return_eval rho (states!lpcl_target middle)) event tt"
    using actual by (simp only: same)
  show ?thesis using lpp_context_cut_action_sound[OF action knowledge child_context child_step] edge silent
    by (meson r_into_trancl trancl_trans)
qed
end
