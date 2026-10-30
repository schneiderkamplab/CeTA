theory LP_Prolog_Integer_Comparison_Check
  imports LP_Prolog_Integer_Test_Check
begin

fun lpp_comparison_descriptor where
  "lpp_comparison_descriptor f LPPIntLess reversed = (f=(if reversed then ''2:>'' else ''2:<''))"
| "lpp_comparison_descriptor f LPPIntLessEqual reversed = (f=(if reversed then ''2:>='' else ''2:=<''))"
| "lpp_comparison_descriptor f LPPIntEqual reversed = (\<not>reversed \<and> f=''2:=:='')"
| "lpp_comparison_descriptor f LPPIntNotEqual reversed = (\<not>reversed \<and> f=map char_of_nat [50,58,61,92,61])"

lemma lpp_comparison_selected:
  "lpp_comparison_descriptor f comparison reversed \<Longrightarrow> (f,2)\<in>lpp_builtin_signature"
  by (cases comparison) (auto simp: lpp_builtin_signature_def split: if_splits)

lemma lpp_fixed_test_step_exact:
  assumes selected: "(f,length ts)\<in>lpp_builtin_signature"
    and exact: "\<And>outcome. U f ts outcome \<longleftrightarrow>
      outcome=(if truth then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure)"
  shows "lpp_answer_transition P lpp_builtin_signature U
    ((LPCGoals (LPCAtom (LPIFun (LPCUser f) ts)#gs),eta)#saved) event tt
    \<longleftrightarrow> event=None \<and> tt=(if truth then (LPCGoals gs,eta)#saved else saved)"
proof (cases truth)
  case True
  have outcomes: "\<And>outcome. U f ts outcome \<longleftrightarrow> outcome=LPPBuiltinSuccess LPIVar"
    by (simp only: exact True if_True)
  show ?thesis using lpp_builtin_success_only[where U=U and P=P and gs=gs and eta=eta and es=saved,
      OF selected outcomes] True by simp
next
  case False
  have outcomes: "\<And>outcome. U f ts outcome \<longleftrightarrow> outcome=LPPBuiltinFailure"
    by (simp only: exact False if_False)
  show ?thesis using lpp_builtin_failure_only[where U=U and P=P and gs=gs and eta=eta and es=saved,
      OF selected outcomes] False by simp
qed

definition lpp_check_integer_comparison_node where
  "lpp_check_integer_comparison_node fuel Q nds states nd ss K f comparison reversed a b ea eb gs active saved yes no =
    (ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved \<and>
     lpp_comparison_descriptor f comparison reversed \<and>
     a=lpp_expression_term ea \<and> b=lpp_expression_term eb \<and>
     lpp_expression_check K ea \<and> lpp_expression_check K eb \<and>
     lpc_check_return_table_link fuel Q nds states nd ((LPCGoals gs,active)#saved)
       (lpcn_ground nd) (lpcn_guards nd) [] (yes::string lpc_link) \<and>
     lpc_check_return_table_link fuel Q nds states nd saved (lpcn_ground nd) (lpcn_guards nd) [] (no::string lpc_link))"

theorem lpp_integer_comparison_node_sound:
  assumes checked: "lpp_check_integer_comparison_node fuel Q nds states nd ss K f comparison reversed a b ea eb gs active saved yes no"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and integers: "lpp_integer_known K eta"
    and exact: "\<And>outcome. U f [lp_ieval a eta,lp_ieval b eta] outcome =
      lpp_integer_compare_outcome comparison
        (if reversed then lp_ieval b eta else lp_ieval a eta)
        (if reversed then lp_ieval a eta else lp_ieval b eta) outcome"
    and step: "lpp_answer_transition P lpp_builtin_signature U (lpc_return_eval eta ss) event tt"
  shows "event=None \<and> (\<exists>u swaps.
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+ \<and>
    lpc_return_rep nds states (lpc_return_scope_word swaps tt) u)"
proof -
  have shape: "ss=(LPCGoals (LPCAtom (Fun (LPCUser f) [a,b])#gs),active)#saved"
    and name: "lpp_comparison_descriptor f comparison reversed"
    and ea: "a=lpp_expression_term ea" and eb: "b=lpp_expression_term eb"
    and ca: "lpp_expression_check K ea" and cb: "lpp_expression_check K eb"
    using checked by (auto simp: lpp_check_integer_comparison_node_def)
  obtain n where left: "lpp_integer_evaluation (lp_ieval a eta) n"
    using lpp_checked_expression_finishes[OF ca integers] ea by blast
  obtain m where right: "lpp_integer_evaluation (lp_ieval b eta) m"
    using lpp_checked_expression_finishes[OF cb integers] eb by blast
  let ?truth = "lpp_integer_compare comparison (if reversed then m else n) (if reversed then n else m)"
  have selected: "(f,length [lp_ieval a eta,lp_ieval b eta])\<in>lpp_builtin_signature"
    using lpp_comparison_selected[OF name] by (simp add: numeral_2_eq_2)
  have outcomes: "\<And>outcome. U f [lp_ieval a eta,lp_ieval b eta] outcome \<longleftrightarrow>
    outcome=(if ?truth then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure)"
    unfolding exact
    by (cases reversed) (use lpp_integer_compare_outcome_exact[OF left right]
      lpp_integer_compare_outcome_exact[OF right left] in simp_all)
  have actual: "event=None \<and> tt=(if ?truth then lpc_return_eval eta ((LPCGoals gs,active)#saved)
      else lpc_return_eval eta saved)"
    using step by (simp add: shape lpc_return_eval_def lpp_fixed_test_step_exact[where U=U and P=P, OF selected outcomes])
  have link: "lpc_check_return_table_link fuel Q nds states nd
      (if ?truth then (LPCGoals gs,active)#saved else saved) (lpcn_ground nd) (lpcn_guards nd) []
      (if ?truth then yes else no)"
    using checked by (auto simp: lpp_check_integer_comparison_node_def)
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  show ?thesis using lpc_return_table_link_sound[OF link equations refl known] actual
    by (auto split: if_splits)
qed

end
