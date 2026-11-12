theory LP_Cut_NO_Return_Trace_Test
 imports LP_Cut_NO_Return_Trace
begin

lemma return_trace_two_checked_steps:
 "lpc_no_return_trace 10 [] [] [(LPCGoals [LPCTrue,LPCFail],[Var ''active''])]
   [(LPCNOAdmin,[(LPCGoals [LPCFail],[Var ''active''])]),(LPCNOAdmin,[])] []"
 by simp

lemma return_trace_rejects_missing_step:
 "\<not> lpc_no_return_trace 10 [] [] [(LPCGoals [LPCTrue,LPCFail],[Var ''active''])]
   [(LPCNOAdmin,[])] []"
 by simp

lemma return_trace_rejects_success_escape:
 "\<not> lpc_no_return_step 10 [] [] [(LPCGoals [],[Var ''active''])] LPCNOAdmin []"
 by simp

lemma return_trace_rejects_saved_environment_change:
 "\<not> lpc_no_return_step 10 [] []
   [(LPCGoals [LPCFail],[Var ''active'']),(LPCGoals [LPCTrue],[Var ''saved''])]
   LPCNOAdmin [(LPCGoals [LPCTrue],[Var ''active''])]"
 by simp

lemma return_trace_rejects_reserved_allocation:
 "\<not> lpc_no_return_step 10 [] [7]
   [(LPCGoals [LPCAtom (Fun (LPCUser ''helper'') [])],[])] (LPCNOCase 7) []"
 by simp

ML \<open>
val checked = [@{thm return_trace_two_checked_steps}, @{thm return_trace_rejects_missing_step},
 @{thm return_trace_rejects_success_escape}, @{thm return_trace_rejects_saved_environment_change},
 @{thm return_trace_rejects_reserved_allocation}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted return-aware trace controls" else ();
\<close>
end
