theory LP_Cut_NO_Permutation_Test
 imports LP_Cut_NO_Return_Permutation LP_Cut_NO_Return_Check_Test
begin

lemma permutation_three_cycle:
 "map (lpc_no_permute [(''R'',''S''),(''S'',''T'')]) [''R'',''S'',''T'',''caller''] =
   [''T'',''R'',''S'',''caller'']"
 by (simp add: lpc_no_swap_def)

lemma permutation_order_matters:
 "lpc_no_permute [(''R'',''S''),(''S'',''T'')] ''R'' \<noteq>
   lpc_no_permute [(''S'',''T''),(''R'',''S'')] ''R''"
 by (simp add: lpc_no_swap_def)

lemma permutation_multiple_returns:
 "lpc_no_return_resolve_permutation 30 return_no_program return_no_call [] 0 0
   return_no_saved [Var ''R'',Var ''S'',Var ''R''] 2 [''$$X''] [Fun (LPCUser ''a'') []]
   [(''R'',''T''),(''S'',''U'')] [] [Var ''T'',Var ''U'',Var ''T'']"
 by (simp only: return_no_program_def return_no_call_def return_no_saved_def; code_simp)

lemma permutation_cycle_returns:
 "lpc_no_return_resolve_permutation 30 return_no_program return_no_call [] 0 0
   return_no_saved [Var ''R'',Var ''S'',Var ''T''] 2 [''$$X''] [Fun (LPCUser ''a'') []]
   [(''R'',''S''),(''S'',''T'')] [] [Var ''T'',Var ''R'',Var ''S'']"
 by (simp only: return_no_program_def return_no_call_def return_no_saved_def; code_simp)

lemma permutation_rejects_merged_returns:
 "\<not>lpc_no_return_resolve_permutation 30 return_no_program return_no_call [] 0 0
   return_no_saved [Var ''R'',Var ''S''] 2 [''$$X''] [Fun (LPCUser ''a'') []]
   [(''R'',''T''),(''S'',''U'')] [] [Var ''T'',Var ''T'']"
 by (simp only: return_no_program_def return_no_call_def return_no_saved_def; code_simp)

lemma permutation_rejects_removed_swap:
 "\<not>lpc_no_return_resolve_permutation 30 return_no_program return_no_call [] 0 0
   return_no_saved [Var ''R'',Var ''S''] 2 [''$$X''] [Fun (LPCUser ''a'') []]
   [(''R'',''T'')] [] [Var ''T'',Var ''U'']"
 by (simp only: return_no_program_def return_no_call_def return_no_saved_def; code_simp)

lemma permutation_rejects_wrong_order:
 "\<not>lpc_no_return_resolve_permutation 30 return_no_program return_no_call [] 0 0
   return_no_saved [Var ''R'',Var ''S'',Var ''T''] 2 [''$$X''] [Fun (LPCUser ''a'') []]
   [(''S'',''T''),(''R'',''S'')] [] [Var ''T'',Var ''R'',Var ''S'']"
 by (simp only: return_no_program_def return_no_call_def return_no_saved_def; code_simp)

lemma permutation_rejects_captured_return:
 "\<not>lpc_no_return_resolve_permutation 30 return_no_program return_no_call [] 0 0
   return_no_saved [Var ''$$X'',Var ''S''] 2 [''$$X''] [Fun (LPCUser ''a'') []]
   [(''R'',''T''),(''S'',''U'')] [] [Fun (LPCUser ''a'') [],Var ''U'']"
 by (simp only: return_no_program_def return_no_call_def return_no_saved_def; code_simp)

ML \<open>
val checked = [@{thm permutation_three_cycle}, @{thm permutation_order_matters},
 @{thm permutation_multiple_returns}, @{thm permutation_cycle_returns},
 @{thm permutation_rejects_merged_returns}, @{thm permutation_rejects_removed_swap},
 @{thm permutation_rejects_wrong_order}, @{thm permutation_rejects_captured_return}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted permutation regressions" else ();
\<close>
end
