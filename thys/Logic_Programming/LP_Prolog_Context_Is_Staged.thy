theory LP_Prolog_Context_Is_Staged
  imports LP_Prolog_Context_Actions
begin

text \<open>Ferrum records evaluation followed by shared unification. Both
control edges represent one source is/2 operation; the intermediate equality
state is not exposed as an already completed Prolog source step.\<close>
definition lpp_check_context_is_staged where
  "lpp_check_context_is_staged fuel P Q nds states contexts nd ss source_context K evidence a e gs active saved result_var middle returned arity action =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved \<and>
     e=lpp_expression_term evidence \<and> lpp_expression_check K evidence \<and>
     lpp_fresh_return result_var ss \<and> lpp_context_fresh result_var source_context \<and>
     result_var\<notin>set (lpcn_vars nd) \<and> list_all (lpp_fresh_guard result_var) (lpcn_guards nd) \<and>
     lpcl_swaps middle=[] \<and>
     lpp_check_context_table_link fuel Q nds states contexts nd
       ((LPCGoals (LPCUnify a (Var result_var)#gs),active)#saved)
       (result_var#lpcn_ground nd) (lpcn_guards nd) []
       (lpp_add_evaluation_observation e (Var result_var) source_context) middle \<and>
     lpp_check_context_cut_action fuel P Q nds states contexts (nds!lpcl_target middle)
       (states!lpcl_target middle) (contexts!lpcl_target middle) returned arity action)"

theorem lpp_context_is_staged_sound:
  assumes checked: "lpp_check_context_is_staged fuel P Q nds states contexts nd ss source_context K evidence a e gs active saved result_var middle returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and observed: "lpp_source_context_holds SP source_context eta"
    and integers: "lpp_integer_known K eta"
    and step: "lpp_answer_transition P lpp_builtin_signature lpp_integer_source_builtin (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps tt) u)"
proof -
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved"
    and expr: "e=lpp_expression_term evidence" and typed: "lpp_expression_check K evidence"
    and result_var: "lpp_fresh_return result_var ss"
    and context_fresh: "lpp_context_fresh result_var source_context"
    and interface: "result_var\<notin>set (lpcn_vars nd)"
    and guards: "list_all (lpp_fresh_guard result_var) (lpcn_guards nd)"
    and swaps: "lpcl_swaps middle=[]"
    and link: "lpp_check_context_table_link fuel Q nds states contexts nd
      ((LPCGoals (LPCUnify a (Var result_var)#gs),active)#saved)
      (result_var#lpcn_ground nd) (lpcn_guards nd) []
      (lpp_add_evaluation_observation e (Var result_var) source_context) middle"
    and action: "lpp_check_context_cut_action fuel P Q nds states contexts (nds!lpcl_target middle)
      (states!lpcl_target middle) (contexts!lpcl_target middle) returned arity action"
    using checked by (auto simp: lpp_check_context_is_staged_def)
  obtain n where evaluated: "lpp_integer_evaluation (lp_ieval e eta) n"
    using lpp_checked_expression_finishes[OF typed integers] expr by blast
  let ?nu = "eta(result_var:=lpp_integer_value n)"
  let ?synthetic = "((LPCGoals (LPCUnify a (Var result_var)#gs),active)#saved)"
  have exact: "\<And>outcome. lpp_integer_source_builtin ''2:is'' [lp_ieval a eta,lp_ieval e eta] outcome =
    lpp_integer_is_outcome (lp_ieval a eta) (lp_ieval e eta) outcome" by simp
  have source: "lpc_answer_transition P
    ((LPCGoals (LPCUnify (lp_ieval a eta) (lpp_integer_value n)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) event tt"
    by (rule lpp_checked_is_uses_shared_equality[where U=lpp_integer_source_builtin, OF evaluated exact])
      (use step in \<open>simp add: shape lpc_return_eval_def\<close>)
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
  have actual: "lpc_answer_transition P (lpc_return_eval ?nu ?synthetic) event tt"
    using source by (simp only: represented)
  have silent: "event=None" using source by (cases rule: lpc_answer_transition.cases) auto
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
  obtain ps gs' os where origin: "lpp_add_evaluation_observation e (Var result_var) source_context=(ps,gs',os)"
    by (cases "lpp_add_evaluation_observation e (Var result_var) source_context") auto
  obtain cps cgs cos where target: "contexts!lpcl_target middle=(cps,cgs,cos)"
    by (cases "contexts!lpcl_target middle") auto
  have base: "lpc_check_return_table_link fuel Q nds states nd ?synthetic
    (result_var#lpcn_ground nd) (lpcn_guards nd) [] middle"
    and transport: "lpp_check_context_transport ps gs' os cps cgs cos (lpcl_bindings middle)"
    using link by (auto simp: lpp_check_context_table_link_def origin target)
  have true_context: "lpp_path_context_holds SP ps gs' os ?nu" using facts by (simp add: origin)
  have equations: "lp_equations [] ?nu" by (simp add: lp_equations_def)
  obtain rho where same: "lpc_return_eval ?nu ?synthetic=lpc_return_eval rho (states!lpcl_target middle)"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target middle))) (lpcn_guards (nds!lpcl_target middle)) rho"
    and child_context: "lpp_path_context_holds SP cps cgs cos rho"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
      [(lpcn_pred (nds!lpcl_target middle),map rho (lpcn_vars (nds!lpcl_target middle)))])\<in>lp_ild Q"
    using lpp_return_context_link_sound[OF base equations parent extended transport true_context] by (simp add: swaps) blast
  have child_facts: "lpp_source_context_holds SP (contexts!lpcl_target middle) rho"
    using child_context by (simp add: target)
  have child_step: "lpc_answer_transition P (lpc_return_eval rho (states!lpcl_target middle)) event tt"
    using actual by (simp only: same)
  show ?thesis using lpp_context_cut_action_sound[OF action knowledge child_facts child_step] edge silent
    by (meson r_into_trancl trancl_trans)
qed

ML \<open>
val checked = [@{thm lpp_context_is_staged_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted staged arithmetic source dependency" else ();
\<close>
end
