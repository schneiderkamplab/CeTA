theory LP_Prolog_Context_Cut_Actions
 imports LP_Prolog_Context_Allocate
begin
fun lpp_check_context_cut_action where
  "lpp_check_context_cut_action fuel P Q nds states contexts nd ss source_context returned arity LPCRTerminal = (ss=[])"
| "lpp_check_context_cut_action fuel P Q nds states contexts nd ss source_context returned arity LPCRInconsistent =
    lp_cut_check_inconsistent (lpcn_guards nd)"
| "lpp_check_context_cut_action fuel P Q nds states contexts nd ss source_context returned arity (LPCRAdmin event next e) =
    lpp_check_context_admin_node fuel Q nds states contexts nd ss source_context returned arity event next e"
| "lpp_check_context_cut_action fuel P Q nds states contexts nd ss source_context returned arity (LPCRCase m f ts gs active saved e) =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved \<and>
     lpp_check_context_case_node fuel P Q nds states contexts nd source_context m f ts gs active saved e)"
| "lpp_check_context_cut_action fuel P Q nds states contexts nd ss source_context returned arity
    (LPCRMeta m a gs active saved body e) =
    (ss=(LPCGoals (LPCMeta a#gs),active)#saved \<and>
     lpp_check_context_meta_node fuel Q nds states contexts nd source_context m a gs active saved body e)"
| "lpp_check_context_cut_action fuel P Q nds states contexts nd ss source_context returned arity
    (LPCREquality a b gs active saved k l next mode outputs yes no) =
    (ss=(LPCGoals (LPCUnify a b#gs),active)#saved \<and>
     lpp_check_context_equality_node fuel P Q nds states contexts nd a b gs active saved k l next mode outputs source_context yes no)"
| "lpp_check_context_cut_action fuel P Q nds states contexts nd ss source_context returned arity
    (LPCRResolution a gs c m active saved k l A next anchors bindings mode outputs yes no) =
    (ss=(LPCClause (LPCAtom a#gs) c m,active)#saved \<and>
     lpp_check_context_resolution_node fuel P Q nds states contexts nd a gs c m active saved k l A next anchors bindings mode outputs source_context yes no)"

theorem lpp_context_cut_action_sound:
  assumes checked: "lpp_check_context_cut_action fuel P Q nds states contexts nd ss source_context returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and observed: "lpp_source_context_holds SP source_context eta"
    and step: "lpc_answer_transition P (lpc_return_eval eta ss) event tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpp_context_return_rep SP nds states contexts (lpc_return_scope_word swaps tt) u) \<and>
    (\<forall>rho. event=Some rho \<longrightarrow>
      ([(lpcn_pred nd,map eta (lpcn_vars nd))],[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
proof (cases action)
  case LPCRTerminal
  then have "ss=[]" using checked by simp
  then show ?thesis using step by (auto simp: lpc_return_eval_def elim: lpc_answer_transition.cases)
next
  case LPCRInconsistent
  have "lp_cut_check_inconsistent (lpcn_guards nd)" using checked LPCRInconsistent by simp
  then show ?thesis using lp_cut_checked_inconsistent[OF _ known] by blast
next
  case (LPCRAdmin emitted successor e)
  then show ?thesis using lpp_context_admin_node_sound[OF _ known observed step] checked by simp
next
  case (LPCRCase m f ts gs active saved e)
  have check: "lpp_check_context_case_node fuel P Q nds states contexts nd source_context m f ts gs active saved e"
    and ss: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved"
    using checked LPCRCase by auto
  have source: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved)) event tt"
    using step ss by simp
  show ?thesis using lpp_context_case_node_sound[OF check known observed source] by auto
next
  case (LPCRMeta m a gs active saved body e)
  have check: "lpp_check_context_meta_node fuel Q nds states contexts nd source_context m a gs active saved body e"
    and ss: "ss=(LPCGoals (LPCMeta a#gs),active)#saved"
    using checked LPCRMeta by auto
  have source: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCMeta a#gs),active)#saved)) event tt"
    using step ss by simp
  show ?thesis using lpp_context_meta_node_sound[OF check known observed source] by auto
next
  case (LPCREquality a b gs active saved k l successor mode outputs yes no)
  have check: "lpp_check_context_equality_node fuel P Q nds states contexts nd a b gs active saved k l successor mode outputs source_context yes no"
    and ss: "ss=(LPCGoals (LPCUnify a b#gs),active)#saved"
    using checked LPCREquality by auto
  have source: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),active)#saved)) event tt"
    using step ss by simp
  show ?thesis using lpp_context_equality_node_sound[OF check known observed source] by auto
next
  case (LPCRResolution a gs c m active saved k l A successor anchors bindings mode outputs yes no)
  have check: "lpp_check_context_resolution_node fuel P Q nds states contexts nd a gs c m active saved k l A successor anchors bindings mode outputs source_context yes no"
    and ss: "ss=(LPCClause (LPCAtom a#gs) c m,active)#saved"
    using checked LPCRResolution by auto
  have source: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCClause (LPCAtom a#gs) c m,active)#saved)) event tt"
    using step ss by simp
  show ?thesis using lpp_context_resolution_node_sound[OF check known observed source] by auto
qed


end
