theory LP_Cut_Return_Check
  imports LP_Cut_Return_Allocate LP_Cut_Return_Table_Equality
begin

datatype 'f lpc_return_action =
    LPCRTerminal
  | LPCRInconsistent
  | LPCRAdmin "'f lpc_term list option" "'f lpc_return_state" "'f lpc_link"
  | LPCRCase nat 'f "'f lpc_term list" "'f lpc_term lp_cut_goal list"
      "'f lpc_term list" "'f lpc_return_state" "'f lpc_link"
  | LPCRMeta nat "'f lpc_term" "'f lpc_term lp_cut_goal list"
      "'f lpc_term list" "'f lpc_return_state" "'f lpc_term lp_cut_goal list" "'f lpc_link"
  | LPCREquality "'f lpc_term" "'f lpc_term" "'f lpc_term lp_cut_goal list"
      "'f lpc_term list" "'f lpc_return_state" nat nat "'f lpc_term lp_cut_goal list"
      lp_cut_coverage "'f lpc_term list" "'f lpc_link" "'f lpc_link"
  | LPCRResolution "'f lpc_term" "'f lpc_term lp_cut_goal list" nat nat
      "'f lpc_term list" "'f lpc_return_state" nat nat "string list"
      "'f lpc_term lp_cut_goal list" "'f lpc_term list" "(string * 'f lpc_term) list"
      lp_cut_coverage "'f lpc_term list" "'f lpc_link" "'f lpc_link"

fun lpc_check_return_action where
  "lpc_check_return_action fuel P Q nds states nd ss returned arity LPCRTerminal = (ss=[])"
| "lpc_check_return_action fuel P Q nds states nd ss returned arity LPCRInconsistent =
    lp_cut_check_inconsistent (lpcn_guards nd)"
| "lpc_check_return_action fuel P Q nds states nd ss returned arity (LPCRAdmin event next e) =
    lpc_check_return_admin_node fuel Q nds states nd ss returned arity event next e"
| "lpc_check_return_action fuel P Q nds states nd ss returned arity (LPCRCase m f ts gs active saved e) =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved \<and>
     lpc_check_return_case_node fuel P Q nds states nd m f ts gs active saved e)"
| "lpc_check_return_action fuel P Q nds states nd ss returned arity
    (LPCRMeta m a gs active saved body e) =
    (ss=(LPCGoals (LPCMeta a#gs),active)#saved \<and>
     lpc_check_return_meta_node fuel Q nds states nd m a gs active saved body e)"
| "lpc_check_return_action fuel P Q nds states nd ss returned arity
    (LPCREquality a b gs active saved k l next mode outputs yes no) =
    (ss=(LPCGoals (LPCUnify a b#gs),active)#saved \<and>
     lpc_check_return_equality_node fuel P Q nds states nd a b gs active saved k l next mode outputs yes no)"
| "lpc_check_return_action fuel P Q nds states nd ss returned arity
    (LPCRResolution a gs c m active saved k l A next anchors bindings mode outputs yes no) =
    (ss=(LPCClause (LPCAtom a#gs) c m,active)#saved \<and>
     lpc_check_return_resolution_node fuel P Q nds states nd a gs c m active saved k l A next anchors bindings mode outputs yes no)"

theorem lpc_return_action_sound:
  assumes checked: "lpc_check_return_action fuel P Q nds states nd ss returned arity action"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and step: "lpc_answer_transition P (lpc_return_eval eta ss) event tt"
  shows "(\<exists>u swaps. ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
      lpc_return_rep nds states (lpc_return_scope_word swaps tt) u) \<and>
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
  then show ?thesis using lpc_return_admin_node_sound[OF _ known step] checked by simp
next
  case (LPCRCase m f ts gs active saved e)
  have check: "lpc_check_return_case_node fuel P Q nds states nd m f ts gs active saved e"
    and ss: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved"
    using checked LPCRCase by auto
  have source: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved)) event tt"
    using step ss by simp
  show ?thesis using lpc_return_case_node_sound[OF check known source] by auto
next
  case (LPCRMeta m a gs active saved body e)
  have check: "lpc_check_return_meta_node fuel Q nds states nd m a gs active saved body e"
    and ss: "ss=(LPCGoals (LPCMeta a#gs),active)#saved"
    using checked LPCRMeta by auto
  have source: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCMeta a#gs),active)#saved)) event tt"
    using step ss by simp
  show ?thesis using lpc_return_meta_node_sound[OF check known source] by auto
next
  case (LPCREquality a b gs active saved k l successor mode outputs yes no)
  have check: "lpc_check_return_equality_node fuel P Q nds states nd a b gs active saved k l successor mode outputs yes no"
    and ss: "ss=(LPCGoals (LPCUnify a b#gs),active)#saved"
    using checked LPCREquality by auto
  have source: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCGoals (LPCUnify a b#gs),active)#saved)) event tt"
    using step ss by simp
  show ?thesis using lpc_return_equality_node_sound[OF check known source] by auto
next
  case (LPCRResolution a gs c m active saved k l A successor anchors bindings mode outputs yes no)
  have check: "lpc_check_return_resolution_node fuel P Q nds states nd a gs c m active saved k l A successor anchors bindings mode outputs yes no"
    and ss: "ss=(LPCClause (LPCAtom a#gs) c m,active)#saved"
    using checked LPCRResolution by auto
  have source: "lpc_answer_transition P
      (lpc_return_eval eta ((LPCClause (LPCAtom a#gs) c m,active)#saved)) event tt"
    using step ss by simp
  show ?thesis using lpc_return_resolution_node_sound[OF check known source] by auto
qed

definition lpc_check_return_table where
  "lpc_check_return_table fuel P Q nds states returned arity actions =
    (length nds=length states \<and> length nds=length actions \<and>
     list_all (\<lambda>i. map fst (states!i)=lpcn_state (nds!i) \<and>
       lpc_check_return_action fuel P Q nds states (nds!i) (states!i) returned arity (actions!i)) [0..<length nds])"

theorem lpc_check_return_table_contract:
  assumes checked: "lpc_check_return_table fuel P Q nds states returned arity actions"
    and program: "lp_cut_source_program P"
    and root: "i<length nds"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  shows "lpc_return_contract P (lpc_return_eval eta (states!i)) (lp_ild Q)
    [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof -
  have valid: "lpc_return_graph_valid P (lp_ild Q)
    (\<lambda>ss t. \<exists>swaps. lpc_return_rep nds states (lpc_return_scope_word swaps ss) t)
    (\<lambda>rho. [(returned,map rho [0..<arity])]) (\<lambda>_. 0)"
  proof (rule lpc_return_graph_scope_valid[OF program])
    fix ss t event tt
    assume rep: "lpc_return_rep nds states ss t"
      and step: "lpc_answer_transition P ss event tt"
    obtain j nu where j: "j<length nds" and ss: "ss=lpc_return_eval nu (states!j)"
      and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) nu"
      and t: "t=[(lpcn_pred (nds!j),map nu (lpcn_vars (nds!j)))]"
      using rep unfolding lpc_return_rep_def by blast
    have action: "lpc_check_return_action fuel P Q nds states (nds!j) (states!j) returned arity (actions!j)"
      using checked j by (auto simp: lpc_check_return_table_def list_all_iff)
    show "(\<exists>u swaps. (t,u)\<in>(lp_ild Q)\<^sup>+ \<and> lpc_return_rep nds states (lpc_return_scope_word swaps tt) u) \<and>
      (\<forall>rho. event=Some rho \<longrightarrow> (t,[(returned,map rho [0..<arity])])\<in>(lp_ild Q)\<^sup>*)"
      using lpc_return_action_sound[OF action knowledge, of event tt] step by (simp add: ss t)
  qed
  have bound: "i<length states" using checked root by (simp add: lpc_check_return_table_def)
  have represented: "\<exists>swaps. lpc_return_rep nds states
    (lpc_return_scope_word swaps (lpc_return_eval eta (states!i)))
    [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]"
    by (rule exI[of _ "[]"], simp only: lpc_return_scope_word.simps,
      unfold lpc_return_rep_def, rule exI[of _ i], rule exI[of _ eta])
      (use root bound known in auto)
  show ?thesis by (rule lpc_return_graph_contract[OF valid residual represented])
qed

end
