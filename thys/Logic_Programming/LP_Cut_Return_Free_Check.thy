theory LP_Cut_Return_Free_Check
  imports LP_Cut_Return_Free_Allocate LP_Cut_Return_Free_Equality LP_Cut_Return_Check
begin

fun lpc_check_return_free_action where
  "lpc_check_return_free_action fuel P Q nds states Fs nd F ss returned arity LPCRTerminal = (ss=[])"
| "lpc_check_return_free_action fuel P Q nds states Fs nd F ss returned arity LPCRInconsistent =
    lp_cut_check_inconsistent (lpcn_guards nd)"
| "lpc_check_return_free_action fuel P Q nds states Fs nd F ss returned arity (LPCRAdmin event next e) =
    lpc_check_return_free_admin_node fuel Q nds states Fs nd F ss returned arity event next e"
| "lpc_check_return_free_action fuel P Q nds states Fs nd F ss returned arity (LPCRCase m f ts gs active saved e) =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved \<and>
     lpc_check_return_free_case_node fuel P Q nds states Fs nd F m f ts gs active saved e)"
| "lpc_check_return_free_action fuel P Q nds states Fs nd F ss returned arity
    (LPCRMeta m a gs active saved body e) =
    (ss=(LPCGoals (LPCMeta a#gs),active)#saved \<and>
     lpc_check_return_free_meta_node fuel Q nds states Fs nd F m a gs active saved body e)"
| "lpc_check_return_free_action fuel P Q nds states Fs nd F ss returned arity
    (LPCREquality a b gs active saved k l next mode outputs yes no) =
    (ss=(LPCGoals (LPCUnify a b#gs),active)#saved \<and>
     lpc_check_return_free_equality_node fuel P Q nds states Fs nd F a b gs active saved k l next mode outputs yes no)"
| "lpc_check_return_free_action fuel P Q nds states Fs nd F ss returned arity
    (LPCRResolution a gs c m active saved k l A next anchors bindings mode outputs yes no) =
    (ss=(LPCClause (LPCAtom a#gs) c m,active)#saved \<and>
     lpc_check_return_free_resolution_node fuel P Q nds states Fs nd F a gs c m active saved k l A next anchors bindings mode outputs yes no)"

theorem lpc_return_free_action_sound:
  assumes checked: "lpc_check_return_free_action fuel P Q nds states Fs nd F ss returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and step: "lpc_answer_transition P (lpc_return_eval eta ss) event tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpc_return_free_rep nds states Fs (lpc_return_scope_word swaps tt) u) \<and>
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
  then show ?thesis using lpc_return_free_admin_node_sound[OF _ known free step] checked by simp
next
  case (LPCRCase m f ts gs active saved e)
  have check: "lpc_check_return_free_case_node fuel P Q nds states Fs nd F m f ts gs active saved e"
    and ss: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved"
    using checked LPCRCase by auto
  have source: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved)) event tt"
    using step ss by simp
  show ?thesis using lpc_return_free_case_node_sound[OF check known free source] by auto
next
  case (LPCRMeta m a gs active saved body e)
  have check: "lpc_check_return_free_meta_node fuel Q nds states Fs nd F m a gs active saved body e"
    and ss: "ss=(LPCGoals (LPCMeta a#gs),active)#saved"
    using checked LPCRMeta by auto
  have source: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCMeta a#gs),active)#saved)) event tt"
    using step ss by simp
  show ?thesis using lpc_return_free_meta_node_sound[OF check known free source] by auto
next
  case (LPCREquality a b gs active saved k l successor mode outputs yes no)
  have check: "lpc_check_return_free_equality_node fuel P Q nds states Fs nd F a b gs active saved k l successor mode outputs yes no"
    and ss: "ss=(LPCGoals (LPCUnify a b#gs),active)#saved"
    using checked LPCREquality by auto
  have source: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),active)#saved)) event tt"
    using step ss by simp
  show ?thesis using lpc_return_free_equality_node_sound[OF check known free source] by auto
next
  case (LPCRResolution a gs c m active saved k l A successor anchors bindings mode outputs yes no)
  have check: "lpc_check_return_free_resolution_node fuel P Q nds states Fs nd F a gs c m active saved k l A successor anchors bindings mode outputs yes no"
    and ss: "ss=(LPCClause (LPCAtom a#gs) c m,active)#saved"
    using checked LPCRResolution by auto
  have source: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCClause (LPCAtom a#gs) c m,active)#saved)) event tt"
    using step ss by simp
  show ?thesis using lpc_return_free_resolution_node_sound[OF check known free source] by auto
qed

end
