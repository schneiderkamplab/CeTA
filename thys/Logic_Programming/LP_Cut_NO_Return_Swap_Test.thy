theory LP_Cut_NO_Return_Swap_Test
 imports LP_Cut_NO_Return_Swap LP_Cut_NO_Return_Check_Test
begin

lemma return_no_swap_preserves_interface:
 "lpc_no_return_resolve_swap 30 return_no_program return_no_call [] 0 0
   return_no_saved [Var ''R''] 2 [''$$X''] [Fun (LPCUser ''a'') []] ''R'' ''S'' [] [Var ''S'']"
 by (simp only: return_no_program_def return_no_call_def return_no_saved_def; code_simp)

lemma return_no_swap_rejects_changed_return:
 "\<not> lpc_no_return_resolve_swap 30 return_no_program return_no_call [] 0 0
   return_no_saved [Var ''R''] 2 [''$$X''] [Fun (LPCUser ''a'') []] ''R'' ''S'' [] [Fun (LPCUser ''a'') []]"
 by (simp only: return_no_program_def return_no_call_def return_no_saved_def; code_simp)

lemma return_no_swap_rejects_captured_interface:
 "\<not> lpc_no_return_resolve_swap 30 return_no_program return_no_call [] 0 0
   return_no_saved [Var ''$$X''] 2 [''$$X''] [Fun (LPCUser ''a'') []] ''R'' ''S'' [] [Fun (LPCUser ''a'') []]"
 by (simp only: return_no_program_def return_no_call_def return_no_saved_def; code_simp)

lemma return_no_swap_rejects_wrong_mgu:
 "\<not> lpc_no_return_resolve_swap 30 return_no_program return_no_call [] 0 0
   return_no_saved [Var ''R''] 2 [''$$X''] [Fun (LPCUser ''b'') []] ''R'' ''S'' [] [Var ''S'']"
 by (simp only: return_no_program_def return_no_call_def return_no_saved_def; code_simp)

lemma return_no_swap_rejects_omitted_return_rename:
 "\<not> lpc_no_return_resolve_swap 30 return_no_program return_no_call [] 0 0
   return_no_saved [Var ''R''] 2 [''$$X''] [Fun (LPCUser ''a'') []] ''R'' ''S'' [] [Var ''R'']"
 by (simp only: return_no_program_def return_no_call_def return_no_saved_def; code_simp)

ML \<open>
val checked = [@{thm return_no_swap_preserves_interface},
 @{thm return_no_swap_rejects_changed_return},
 @{thm return_no_swap_rejects_captured_interface},
 @{thm return_no_swap_rejects_wrong_mgu}, @{thm return_no_swap_rejects_omitted_return_rename}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted return-aware output swap regression" else ();
\<close>
end
