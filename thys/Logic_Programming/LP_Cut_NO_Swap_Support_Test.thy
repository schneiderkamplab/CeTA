theory LP_Cut_NO_Swap_Support_Test
 imports LP_Cut_NO_Renamed_Unify
begin

lemma output_swap_support_includes_renamed_variables:
 "lpc_conjugate_substitution id (\<lambda>z. Var (lpc_no_swap ''A'' ''B'' z)) ''B'' = Var ''A''"
 by (simp add: lpc_conjugate_substitution_def lpc_no_swap_def)

lemma output_swap_freshening_preserves_caller_only_variable:
 "lpc_conjugate_substitution (lpc_no_swap ''B'' ''fresh'')
   (\<lambda>z. Var (lpc_no_swap ''A'' ''B'' z)) ''B'' = Var ''B''"
 by (simp add: lpc_conjugate_substitution_def lpc_no_swap_def)

lemma output_swap_freshening_updates_shared_output:
 "lpc_conjugate_substitution (lpc_no_swap ''B'' ''fresh'')
   (\<lambda>z. Var (lpc_no_swap ''A'' ''B'' z)) ''A'' = Var ''fresh''"
 by (simp add: lpc_conjugate_substitution_def lpc_no_swap_def)

lemma output_swap_freshening_preserves_caller_sharing:
 "Fun ''pair'' [Var ''B'',Var ''B'']\<cdot>
   lpc_conjugate_substitution (lpc_no_swap ''B'' ''fresh'')
     (\<lambda>z. Var (lpc_no_swap ''A'' ''B'' z)) = Fun ''pair'' [Var ''B'',Var ''B'']"
 by (simp add: output_swap_freshening_preserves_caller_only_variable)

lemma output_swap_does_not_preserve_solved_form_factor:
 "\<not> lpc_global_mgu [] (\<lambda>z. (Var (lpc_no_swap ''A'' ''B'' z) :: (string,string) term))"
proof
 assume bad: "lpc_global_mgu [] (\<lambda>z. (Var (lpc_no_swap ''A'' ''B'' z) :: (string,string) term))"
 have solution: "lp_equations [] (LPIVar :: string \<Rightarrow> (string,string) lp_iterm)"
   by (simp add: lp_equations_def)
 have factor: "lp_ieval (Var (lpc_no_swap ''A'' ''B'' ''A'') :: (string,string) term) LPIVar = LPIVar ''A''"
   by (rule lpc_global_mgu_factor[OF bad solution])
 show False using factor by (simp add: lpc_no_swap_def)
qed

ML \<open>
val checked = [@{thm output_swap_support_includes_renamed_variables},
 @{thm output_swap_freshening_preserves_caller_only_variable}, @{thm output_swap_freshening_updates_shared_output},
 @{thm output_swap_freshening_preserves_caller_sharing}, @{thm output_swap_does_not_preserve_solved_form_factor}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted fresh output swap controls" else ();
\<close>
end
