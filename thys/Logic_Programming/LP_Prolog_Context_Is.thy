theory LP_Prolog_Context_Is
  imports LP_Prolog_Context_Equality
begin

definition lpp_context_fresh where
  "lpp_context_fresh x source_context =
    (\<forall>t\<in>set (lpp_context_terms source_context). x\<notin>vars_term t)"

lemma lpp_context_fresh_eval:
  "lpp_context_fresh x source_context \<Longrightarrow>
    lpp_source_context_holds P source_context (eta(x:=v))=lpp_source_context_holds P source_context eta"
  by (rule lpp_context_environment_cong) (auto simp: lpp_context_fresh_def intro: lpp_fresh_term_eval)

fun lpp_add_evaluation_observation where
  "lpp_add_evaluation_observation e t (facts,guards,observations) =
    (facts,guards@[LPPSEvaluates e t],observations@[LPPOEvaluation e t])"

lemma lpp_add_evaluation_observation_holds:
  "lpp_source_context_holds P source_context eta \<Longrightarrow> lpp_integer_result (lp_ieval e eta) (lp_ieval t eta) \<Longrightarrow>
    lpp_source_context_holds P (lpp_add_evaluation_observation e t source_context) eta"
  by (cases source_context) (auto simp: lpp_path_context_holds_def)

definition lpp_check_context_is_node where
  "lpp_check_context_is_node fuel P Q nds states contexts nd ss source_context K evidence a e gs active saved result_var k l next mode outputs yes no =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved \<and>
     lpcn_state nd=map fst ss \<and>
     e=lpp_expression_term evidence \<and> lpp_expression_check K evidence \<and>
     lpp_fresh_return result_var ss \<and> lpp_context_fresh result_var source_context \<and> result_var\<notin>set (lpcn_vars nd) \<and>
     list_all (lpp_fresh_guard result_var) (lpcn_guards nd) \<and>
     lpp_check_context_equality_node fuel P Q nds states contexts
       (nd\<lparr>lpcn_state:=LPCGoals (LPCUnify a (Var result_var)#gs)#map fst saved, lpcn_ground:=result_var#lpcn_ground nd\<rparr>) a (Var result_var) gs active saved k l next mode outputs (lpp_add_evaluation_observation e (Var result_var) source_context) yes no)"

theorem lpp_context_is_node_sound:
  assumes checked: "lpp_check_context_is_node fuel P Q nds states contexts nd ss source_context K evidence a e gs active saved result_var k l next mode outputs yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and observed: "lpp_source_context_holds SP source_context eta"
    and integers: "lpp_integer_known K eta"
    and exact: "\<And>outcome. U ''2:is'' [lp_ieval a eta,lp_ieval e eta] outcome =
      lpp_integer_is_outcome (lp_ieval a eta) (lp_ieval e eta) outcome"
    and step: "lpp_answer_transition P lpp_builtin_signature U (lpc_return_eval eta ss) event tt"
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
    and equality: "lpp_check_context_equality_node fuel P Q nds states contexts
      (nd\<lparr>lpcn_state:=LPCGoals (LPCUnify a (Var result_var)#gs)#map fst saved, lpcn_ground:=result_var#lpcn_ground nd\<rparr>) a (Var result_var) gs active saved k l next mode outputs (lpp_add_evaluation_observation e (Var result_var) source_context) yes no"
    using checked by (auto simp: lpp_check_context_is_node_def)
  obtain n where evaluated: "lpp_integer_evaluation (lp_ieval e eta) n"
    using lpp_checked_expression_finishes[OF typed integers] expr by blast
  let ?nu = "eta(result_var:=lpp_integer_value n)"
  have source: "lpc_answer_transition P
    ((LPCGoals (LPCUnify (lp_ieval a eta) (lpp_integer_value n)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved) event tt"
    by (rule lpp_checked_is_uses_shared_equality[where U=U, OF evaluated exact])
      (use step in \<open>simp add: shape lpc_return_eval_def\<close>)
  have fa: "result_var\<notin>vars_term a" and rest:
    "lpp_fresh_return result_var ((LPCGoals gs,active)#saved)"
    using result_var by (auto simp: shape lpp_fresh_return_def)
  have unchanged: "lpc_return_eval ?nu ((LPCGoals gs,active)#saved)=lpc_return_eval eta ((LPCGoals gs,active)#saved)"
    by (rule lpp_fresh_return_eval[OF rest])
  have represented: "lpc_return_eval ?nu ((LPCGoals (LPCUnify a (Var result_var)#gs),active)#saved) =
    ((LPCGoals (LPCUnify (lp_ieval a eta) (lpp_integer_value n)#map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs),
      lpc_return_env active eta)#lpc_return_eval eta saved)"
    using unchanged lpp_fresh_term_eval[OF fa, of eta "lpp_integer_value n"]
    by (simp add: lpc_return_eval_def)
  have extended: "lp_cut_knowledge (set (lpcn_ground (nd\<lparr>lpcn_state:=LPCGoals (LPCUnify a (Var result_var)#gs)#map fst saved, lpcn_ground:=result_var#lpcn_ground nd\<rparr>)))
      (lpcn_guards (nd\<lparr>lpcn_state:=LPCGoals (LPCUnify a (Var result_var)#gs)#map fst saved, lpcn_ground:=result_var#lpcn_ground nd\<rparr>)) ?nu"
    using lpp_fresh_integer_knowledge[OF known guards, of n] by simp
  have actual: "lpc_answer_transition P (lpc_return_eval ?nu
    ((LPCGoals (LPCUnify a (Var result_var)#gs),active)#saved)) event tt"
    using source by (simp only: represented)
  have parent: "map ?nu (lpcn_vars nd)=map eta (lpcn_vars nd)"
    using interface by (auto intro!: map_cong)
  have old_context: "lpp_source_context_holds SP source_context ?nu"
    using lpp_context_fresh_eval[OF context_fresh, of SP eta "lpp_integer_value n"] observed by simp
  have fe: "result_var\<notin>vars_term e"
    using result_var by (auto simp: shape lpp_fresh_return_def)
  have evaluation: "lpp_integer_result (lp_ieval e ?nu) (lp_ieval (Var result_var) ?nu)"
    using evaluated by (simp add: lpp_fresh_term_eval[OF fe] lpp_integer_result_def)
  have facts: "lpp_source_context_holds SP (lpp_add_evaluation_observation e (Var result_var) source_context) ?nu"
    by (rule lpp_add_evaluation_observation_holds[OF old_context evaluation])
  show ?thesis using lpp_context_equality_node_sound[OF equality extended facts actual]
    by (simp add: parent)
qed

ML \<open>
val checked = [@{thm lpp_context_is_node_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted contextual source step dependency" else ();
\<close>
end
