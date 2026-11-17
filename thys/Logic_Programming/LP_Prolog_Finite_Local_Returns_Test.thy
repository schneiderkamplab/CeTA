theory LP_Prolog_Finite_Local_Returns_Test
 imports LP_Prolog_Finite_Local_Returns
begin

lemma complete_return_dependencies:
 "lpp_check_finite_return_goals {(''resume'',2)} [''xs'',''n'']
   [LPCAtom (Fun (LPCUser ''resume'') [Var ''xs'',Var ''n''])]"
 by (simp add: lpp_check_finite_return_goals_def)

lemma missing_return_dependency:
 "\<not> lpp_check_finite_return_goals {(''resume'',2)} [''xs'']
   [LPCAtom (Fun (LPCUser ''resume'') [Var ''xs'',Var ''n''])]"
 by (simp add: lpp_check_finite_return_goals_def)

lemma missing_continuation_signature:
 "\<not> lpp_check_finite_return_goals {} [''xs'',''n'']
   [LPCAtom (Fun (LPCUser ''resume'') [Var ''xs'',Var ''n''])]"
 by (simp add: lpp_check_finite_return_goals_def)

lemma dynamic_continuation_rejected:
 "\<not> lpp_check_finite_return_goals A [''goal''] [LPCAtom (Var ''goal'')]"
 by (simp add: lpp_check_finite_return_goals_def)

lemma unused_answer_values_unrestricted:
 assumes "lpp_finite_term (eta ''xs'')" "lpp_finite_term (eta ''n'')"
 shows "lpp_finite_direct_invariant {(''resume'',2)}
   (lpc_return_eval eta [(LPCGoals [LPCAtom (Fun (LPCUser ''resume'') [Var ''xs'',Var ''n''])], outputs)])"
 by (rule lpp_checked_finite_return_goals[OF complete_return_dependencies])
   (use assms in auto)

ML \<open>
val checked = [@{thm complete_return_dependencies}, @{thm missing_return_dependency},
 @{thm missing_continuation_signature}, @{thm dynamic_continuation_rejected},
 @{thm unused_answer_values_unrestricted}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite local return tests" else ();
\<close>
end
