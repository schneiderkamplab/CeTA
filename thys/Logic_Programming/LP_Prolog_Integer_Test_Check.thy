theory LP_Prolog_Integer_Test_Check
  imports LP_Prolog_Arithmetic_Return_Check
begin

definition lpp_integer_test_outcome ::
  "(string lp_cut_symbol,'w) lp_iterm \<Rightarrow> (string,'w) lpp_builtin_result \<Rightarrow> bool" where
  "lpp_integer_test_outcome a outcome =
    (outcome=(if lpp_is_integer a then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure))"

lemma lpp_integer_test_step_exact:
  assumes exact: "\<And>outcome. U ''1:integer'' [a] outcome = lpp_integer_test_outcome a outcome"
  shows "lpp_answer_transition P lpp_builtin_signature U
    ((LPCGoals (LPCAtom (LPIFun (LPCUser ''1:integer'') [a])#gs),eta)#saved) event tt
    \<longleftrightarrow> event=None \<and> tt=(if lpp_is_integer a then (LPCGoals gs,eta)#saved else saved)"
proof (cases "lpp_is_integer a")
  case True
  have selected: "(''1:integer'',length [a])\<in>lpp_builtin_signature"
    by (simp add: lpp_builtin_signature_def)
  have outcomes: "\<And>outcome. U ''1:integer'' [a] outcome \<longleftrightarrow> outcome=LPPBuiltinSuccess LPIVar"
    by (simp only: exact lpp_integer_test_outcome_def True if_True)
  show ?thesis using lpp_builtin_success_only[where U=U and P=P and gs=gs and eta=eta and es=saved,
      OF selected outcomes] True by simp
next
  case False
  have selected: "(''1:integer'',length [a])\<in>lpp_builtin_signature"
    by (simp add: lpp_builtin_signature_def)
  have outcomes: "\<And>outcome. U ''1:integer'' [a] outcome \<longleftrightarrow> outcome=LPPBuiltinFailure"
    by (simp only: exact lpp_integer_test_outcome_def False if_False)
  show ?thesis using lpp_builtin_failure_only[where U=U and P=P and gs=gs and eta=eta and es=saved,
      OF selected outcomes] False by simp
qed

definition lpp_check_integer_test_node where
  "lpp_check_integer_test_node fuel Q nds states nd ss a gs active saved yes no =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser ''1:integer'') [a])#gs),active)#saved \<and>
     lpc_check_return_table_link fuel Q nds states nd ((LPCGoals gs,active)#saved)
       (lpcn_ground nd@sorted_list_of_set (vars_term a)) (lpcn_guards nd) [] yes \<and>
     lpc_check_return_table_link fuel Q nds states nd saved (lpcn_ground nd) (lpcn_guards nd) [] no)"

theorem lpp_integer_test_node_sound:
  assumes checked: "lpp_check_integer_test_node fuel Q nds states nd ss a gs active saved yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and exact: "\<And>outcome. U ''1:integer'' [lp_ieval a eta] outcome = lpp_integer_test_outcome (lp_ieval a eta) outcome"
    and step: "lpp_answer_transition P lpp_builtin_signature U (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpc_return_rep nds states (lpc_return_scope_word swaps tt) u)"
proof -
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser ''1:integer'') [a])#gs),active)#saved"
    using checked by (simp add: lpp_check_integer_test_node_def)
  have actual: "event=None \<and> tt=(if lpp_is_integer (lp_ieval a eta)
    then lpc_return_eval eta ((LPCGoals gs,active)#saved) else lpc_return_eval eta saved)"
    using step by (simp add: shape lpc_return_eval_def lpp_integer_test_step_exact[where U=U, OF exact])
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  show ?thesis
  proof (cases "lpp_is_integer (lp_ieval a eta)")
    case True
    have ground: "lp_seg_ground (lp_ieval a eta)"
      using True by (auto simp: lpp_is_integer_def lpp_integer_value_def)
    have extended: "lp_cut_knowledge (set (lpcn_ground nd@sorted_list_of_set (vars_term a))) (lpcn_guards nd) eta"
      using ground known by (auto simp: lp_cut_knowledge_def lp_seg_ground_eval)
    have link: "lpc_check_return_table_link fuel Q nds states nd ((LPCGoals gs,active)#saved)
      (lpcn_ground nd@sorted_list_of_set (vars_term a)) (lpcn_guards nd) [] yes"
      using checked by (simp add: lpp_check_integer_test_node_def)
    show ?thesis using lpc_return_table_link_sound[OF link equations refl extended] actual True by simp
  next
    case False
    have link: "lpc_check_return_table_link fuel Q nds states nd saved (lpcn_ground nd) (lpcn_guards nd) [] no"
      using checked by (simp add: lpp_check_integer_test_node_def)
    show ?thesis using lpc_return_table_link_sound[OF link equations refl known] actual False by simp
  qed
qed

end
