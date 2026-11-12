theory LP_Prolog_NO_Return_Builtin_Test
 imports LP_Prolog_NO_Renamed_Binary64 LP_Source_Owned_Trace
begin

lemma machine_return_preserves_caller_variable:
 "lpc_conjugate_substitution (lpc_no_swap ''private'' ''fresh'')
   (Var(''private'':=lpp_machine_term (LPPMachineInteger 1))) ''private'' = Var ''private''"
 by (simp add: lpc_conjugate_substitution_def lpc_no_swap_def)

lemma machine_return_updates_fresh_variable:
 "lpc_conjugate_substitution (lpc_no_swap ''private'' ''fresh'')
   (Var(''private'':=lpp_machine_term (LPPMachineInteger 1))) ''fresh'' =
   lpp_machine_term (LPPMachineInteger 1)"
 by (simp add: lpc_conjugate_substitution_def lpc_no_swap_def lpp_integer_term_def)

lemma machine_return_rejects_incompatible_value:
 "lpp_machine_unifier (Fun (LPCUser f) [Var (x::string)]) (LPPMachineInteger 1) = None"
 by (simp add: lpp_integer_term_def)

lemma machine_return_failed_guard_keeps_saved_environment:
 assumes selected: "(f,length input_terms)\<in>lpp_builtin_signature"
   and failed: "U f input_terms LPPBuiltinFailure"
 shows "(lpc_attach rest ((LPCGoals (LPCAtom (LPIFun (LPCUser f) input_terms)#gs),active)#
     [(LPCGoals hs,saved)]), lpc_attach rest [(LPCGoals hs,saved)])\<in>lpp_builtin_source P U"
 by (rule lpp_return_failure_attach_source[where U=U and f=f and input_terms=input_terms, OF selected failed])

lemma machine_return_error_cannot_extend_trace:
 "(s,[])\<notin>lpp_owned_trace_relation P U bs"
 by (simp add: lpp_owned_trace_relation_def)

ML \<open>
val checked = [@{thm machine_return_preserves_caller_variable},
 @{thm machine_return_updates_fresh_variable}, @{thm machine_return_rejects_incompatible_value},
 @{thm machine_return_failed_guard_keeps_saved_environment}, @{thm machine_return_error_cannot_extend_trace}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted builtin return controls" else ();
\<close>
end
