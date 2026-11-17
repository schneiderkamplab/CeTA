theory LP_Prolog_Separation_Ordinary_Tests
 imports LP_Prolog_Separation_Ordinary_Check
begin

text \<open>These checks concern local side conditions only. Positive side checks
still require the existing source-action checker and residual proof.\<close>

lemma lpp_separation_ordinary_test_positive:
 "lpcl_target yes=0 \<Longrightarrow> lpcl_target no=0 \<Longrightarrow>
  lpp_check_separation_ordinary [[]]
   ((LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved)
   (LPPFTest yes no fs ns)"
 by (simp add: lpp_empty_separation_target_def)

lemma lpp_separation_ordinary_is_positive:
 "lpcl_target middle=0 \<Longrightarrow>
  lpp_check_separation_ordinary [[]]
   ((LPCGoals (LPCAtom (Fun (LPCUser ''2:is'') [a,e])#gs),active)#saved)
   (LPPFIs result_var middle fs)"
 by (simp add: lpp_empty_separation_target_def)

lemma lpp_separation_ordinary_missing_context_rejected:
 "\<not>lpp_empty_separation_target [] e"
 by (simp add: lpp_empty_separation_target_def)

lemma lpp_separation_ordinary_unproved_fact_rejected:
 "separation_contexts!lpcl_target e\<noteq>[] \<Longrightarrow>
  \<not>lpp_empty_separation_target separation_contexts e"
 by (simp add: lpp_empty_separation_target_def)

lemma lpp_separation_ordinary_missing_failure_rejected:
 "lpcl_target no\<ge>length separation_contexts \<Longrightarrow>
  \<not>lpp_check_separation_ordinary separation_contexts
   ((LPCGoals (LPCAtom (Fun (LPCUser f) [a])#gs),active)#saved)
   (LPPFTest yes no fs ns)"
 by (simp add: lpp_empty_separation_target_def)

lemma lpp_separation_ordinary_missing_alternative_rejected:
 "length links\<noteq>length ss \<Longrightarrow>
  \<not>lpp_check_separation_ordinary separation_contexts ss (LPPFParallel links factss)"
 by simp

lemma lpp_separation_ordinary_nonempty_terminal_rejected:
 "ss\<noteq>[] \<Longrightarrow>
  \<not>lpp_check_separation_ordinary separation_contexts ss (LPPFCut LPCRTerminal fs ns)"
 by simp

lemma lpp_separation_ordinary_wrong_test_arity_rejected:
 "length ts\<noteq>1 \<Longrightarrow>
  \<not>lpp_check_separation_ordinary separation_contexts
   ((LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved)
   (LPPFTest yes no fs ns)"
 by simp

lemma lpp_separation_ordinary_wrong_is_name_rejected:
 "f\<noteq>''2:is'' \<Longrightarrow>
  \<not>lpp_check_separation_ordinary separation_contexts
   ((LPCGoals (LPCAtom (Fun (LPCUser f) [a,e])#gs),active)#saved)
   (LPPFIs result_var middle fs)"
 by simp

lemma lpp_separation_ordinary_univ_obligation_retained:
 "\<not>lpp_check_separation_ordinary separation_contexts ss (LPPFUniv v n a e fs)"
 by simp

lemma lpp_separation_ordinary_equality_obligation_retained:
 "\<not>lpp_check_separation_ordinary separation_contexts ss
   (LPPFCut (LPCREquality a b gs active saved k l next mode outputs yes no) fs ns)"
 by simp

lemma lpp_separation_ordinary_resolution_obligation_retained:
 "\<not>lpp_check_separation_ordinary separation_contexts ss
   (LPPFCut (LPCRResolution a gs c m active saved k l A next anchors bindings mode outputs yes no) fs ns)"
 by simp

ML \<open>
val checked = @{thms lpp_separation_ordinary_test_positive lpp_separation_ordinary_is_positive
 lpp_separation_ordinary_missing_context_rejected lpp_separation_ordinary_unproved_fact_rejected
 lpp_separation_ordinary_missing_failure_rejected lpp_separation_ordinary_missing_alternative_rejected
 lpp_separation_ordinary_nonempty_terminal_rejected lpp_separation_ordinary_wrong_test_arity_rejected
 lpp_separation_ordinary_wrong_is_name_rejected lpp_separation_ordinary_univ_obligation_retained
 lpp_separation_ordinary_equality_obligation_retained lpp_separation_ordinary_resolution_obligation_retained};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted ordinary separation regressions" else ();
\<close>
end
