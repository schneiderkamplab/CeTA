theory LP_Prolog_Evaluation_Cut_Actions
 imports LP_Prolog_Evaluation_Resolution
begin
fun lpp_check_evaluation_cut_action where
  "lpp_check_evaluation_cut_action T yes_facts no_facts fuel P Q nds states contexts Fs nd F ss source_context returned arity LPCRTerminal = (ss=[])"
| "lpp_check_evaluation_cut_action T yes_facts no_facts fuel P Q nds states contexts Fs nd F ss source_context returned arity LPCRInconsistent =
    lp_cut_check_inconsistent (lpcn_guards nd)"
| "lpp_check_evaluation_cut_action T yes_facts no_facts fuel P Q nds states contexts Fs nd F ss source_context returned arity (LPCRAdmin event next e) =
    lpp_check_evaluation_admin_node T yes_facts fuel Q nds states contexts Fs nd F ss source_context returned arity event next e"
| "lpp_check_evaluation_cut_action T yes_facts no_facts fuel P Q nds states contexts Fs nd F ss source_context returned arity (LPCRCase m f ts gs active saved e) =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved \<and>
     lpp_check_evaluation_case_node T yes_facts fuel P Q nds states contexts Fs nd F source_context m f ts gs active saved e)"
| "lpp_check_evaluation_cut_action T yes_facts no_facts fuel P Q nds states contexts Fs nd F ss source_context returned arity
    (LPCRMeta m a gs active saved body e) =
    (ss=(LPCGoals (LPCMeta a#gs),active)#saved \<and>
     lpp_check_evaluation_meta_node T yes_facts fuel Q nds states contexts Fs nd F source_context m a gs active saved body e)"
| "lpp_check_evaluation_cut_action T yes_facts no_facts fuel P Q nds states contexts Fs nd F ss source_context returned arity
    (LPCREquality a b gs active saved k l next mode outputs yes no) =
    (ss=(LPCGoals (LPCUnify a b#gs),active)#saved \<and>
     lpp_check_evaluation_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs nd F a b gs active saved k l next mode outputs source_context yes no)"
| "lpp_check_evaluation_cut_action T yes_facts no_facts fuel P Q nds states contexts Fs nd F ss source_context returned arity
    (LPCRResolution a gs c m active saved k l A next anchors bindings mode outputs yes no) =
    (ss=(LPCClause (LPCAtom a#gs) c m,active)#saved \<and>
     lpp_check_evaluation_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs nd F a gs c m active saved k l A next anchors bindings mode outputs source_context yes no)"

theorem lpp_evaluation_cut_action_sound:
  fixes SP :: "string lpp_success_clause list"
  assumes contract: "lpp_eval_integer_contract TYPE(string) E"
    and evaluation: "\<And>e t. E e t \<Longrightarrow> lp_seg_ground e \<and> lp_seg_ground t"
    and stable: "\<And>e t sigma. E e t \<Longrightarrow> E (lp_isubst e sigma) (lp_isubst t sigma)"
    and program: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_evaluation_cut_action T yes_facts no_facts fuel P Q nds states contexts Fs nd F ss source_context returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and observed: "lpp_evaluation_context_holds E SP source_context eta"
    and step: "lpc_answer_transition P (lpc_return_eval eta ss) event tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpp_evaluation_rep E SP nds states contexts Fs (lpc_return_scope_word swaps tt) u) \<and>
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
  then show ?thesis using lpp_evaluation_admin_node_sound[OF contract evaluation stable program _ known free observed step] checked by simp
next
  case (LPCRCase m f ts gs active saved e)
  have check: "lpp_check_evaluation_case_node T yes_facts fuel P Q nds states contexts Fs nd F source_context m f ts gs active saved e"
    and ss: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved"
    using checked LPCRCase by auto
  have source: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved)) event tt"
    using step ss by simp
  show ?thesis using lpp_evaluation_case_node_sound[OF contract evaluation stable program check known free observed source] by auto
next
  case (LPCRMeta m a gs active saved body e)
  have check: "lpp_check_evaluation_meta_node T yes_facts fuel Q nds states contexts Fs nd F source_context m a gs active saved body e"
    and ss: "ss=(LPCGoals (LPCMeta a#gs),active)#saved"
    using checked LPCRMeta by auto
  have source: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCMeta a#gs),active)#saved)) event tt"
    using step ss by simp
  show ?thesis using lpp_evaluation_meta_node_sound[OF contract evaluation stable program check known free observed source] by auto
next
  case (LPCREquality a b gs active saved k l successor mode outputs yes no)
  have check: "lpp_check_evaluation_equality_node T yes_facts no_facts fuel P Q nds states contexts Fs nd F a b gs active saved k l successor mode outputs source_context yes no"
    and ss: "ss=(LPCGoals (LPCUnify a b#gs),active)#saved"
    using checked LPCREquality by auto
  have source: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),active)#saved)) event tt"
    using step ss by simp
  show ?thesis using lpp_evaluation_equality_node_sound[OF contract evaluation stable program check known free observed source] by auto
next
  case (LPCRResolution a gs c m active saved k l A successor anchors bindings mode outputs yes no)
  have check: "lpp_check_evaluation_resolution_node T yes_facts no_facts fuel P Q nds states contexts Fs nd F a gs c m active saved k l A successor anchors bindings mode outputs source_context yes no"
    and ss: "ss=(LPCClause (LPCAtom a#gs) c m,active)#saved"
    using checked LPCRResolution by auto
  have source: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCClause (LPCAtom a#gs) c m,active)#saved)) event tt"
    using step ss by simp
  show ?thesis using lpp_evaluation_resolution_node_sound[OF contract evaluation stable program check known free observed source] by auto
qed


end
