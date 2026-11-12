theory LP_Cut_NO_Return_Check_Test
 imports LP_Cut_NO_Return_Check
begin

definition return_no_program :: "(string,string) lp_cut_program" where
 "return_no_program = [(Fun (LPCUser ''helper'') [Var ''X''],[])]"
definition return_no_call :: "(string lp_cut_symbol,string) term" where
 "return_no_call = Fun (LPCUser ''helper'') [Fun (LPCUser ''a'') []]"
definition return_no_saved :: "((string lp_cut_symbol,string) term lp_cut_entry \<times> (string lp_cut_symbol,string) term list) list" where
 "return_no_saved = [(LPCGoals [LPCAtom (Fun (LPCUser ''later'') [Var ''R''])],[Var ''R''])]"

lemma return_no_resolution_preserves_interface:
 "lpc_no_return_resolve 30 return_no_program return_no_call [] 0 0
   return_no_saved [Var ''R''] 2 [''$$X''] [Fun (LPCUser ''a'') []] [] [Var ''R'']"
 by (simp only: return_no_program_def return_no_call_def return_no_saved_def; code_simp)

lemma return_no_resolution_rejects_changed_return:
 "\<not> lpc_no_return_resolve 30 return_no_program return_no_call [] 0 0
   return_no_saved [Var ''R''] 2 [''$$X''] [Fun (LPCUser ''a'') []] [] [Fun (LPCUser ''a'') []]"
 by (simp only: return_no_program_def return_no_call_def return_no_saved_def; code_simp)

lemma return_no_resolution_rejects_captured_interface:
 "\<not> lpc_no_return_resolve 30 return_no_program return_no_call [] 0 0
   return_no_saved [Var ''$$X''] 2 [''$$X''] [Fun (LPCUser ''a'') []] [] [Fun (LPCUser ''a'') []]"
 by (simp only: return_no_program_def return_no_call_def return_no_saved_def; code_simp)

lemma return_no_resolution_rejects_wrong_mgu:
 "\<not> lpc_no_return_resolve 30 return_no_program return_no_call [] 0 0
   return_no_saved [Var ''R''] 2 [''$$X''] [Fun (LPCUser ''b'') []] [] [Var ''R'']"
 by (simp only: return_no_program_def return_no_call_def return_no_saved_def; code_simp)

ML \<open>
val checked = [@{thm return_no_resolution_preserves_interface},
 @{thm return_no_resolution_rejects_changed_return},
 @{thm return_no_resolution_rejects_captured_interface},
 @{thm return_no_resolution_rejects_wrong_mgu}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted return-aware resolution regression" else ();
\<close>
end
