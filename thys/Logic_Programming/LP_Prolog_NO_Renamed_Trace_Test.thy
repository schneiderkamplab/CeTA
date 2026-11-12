theory LP_Prolog_NO_Renamed_Trace_Test
 imports LP_Prolog_NO_Renamed_Trace
begin

text \<open>A finite evaluation-and-guard path with an attached caller variable.
This checks composition and capture avoidance, not a recurring root.\<close>

definition fresh_machine_start :: "((string lp_cut_symbol,string) term lp_cut_entry \<times> (string lp_cut_symbol,string) term list) list" where
 "fresh_machine_start=[(LPCGoals [
   LPCAtom (Fun (LPCUser ''2:is'') [Var ''X'',lpp_machine_term (LPPMachineInteger 1)]),
   LPCAtom (Fun (LPCUser ''2:>'') [Var ''X'',lpp_machine_term (LPPMachineInteger 0)]),
   LPCAtom (Fun (LPCUser ''again'') [])],[Var ''X''])]"
definition fresh_machine_middle :: "((string lp_cut_symbol,string) term lp_cut_entry \<times> (string lp_cut_symbol,string) term list) list" where
 "fresh_machine_middle=[(LPCGoals [
   LPCAtom (Fun (LPCUser ''2:>'') [lpp_machine_term (LPPMachineInteger 1),lpp_machine_term (LPPMachineInteger 0)]),
   LPCAtom (Fun (LPCUser ''again'') [])],[lpp_machine_term (LPPMachineInteger 1)])]"
definition fresh_machine_end :: "((string lp_cut_symbol,string) term lp_cut_entry \<times> (string lp_cut_symbol,string) term list) list" where
 "fresh_machine_end=[(LPCGoals [LPCAtom (Fun (LPCUser ''again'') [])],[lpp_machine_term (LPPMachineInteger 1)])]"
definition fresh_machine_steps where
 "fresh_machine_steps=[(LPPMIs (LPPMachineLiteral (LPPMachineInteger 1)),fresh_machine_middle),
   (LPPMCompare (LPPMachineLiteral (LPPMachineInteger 1)) (LPPMachineLiteral (LPPMachineInteger 0)) True,
      fresh_machine_end)]"

lemma fresh_machine_trace_checked:
 "lpp_no_return_trace 10 [] [] fresh_machine_start fresh_machine_steps fresh_machine_end"
 by (simp add: fresh_machine_start_def fresh_machine_middle_def fresh_machine_end_def fresh_machine_steps_def
   lpp_no_return_comparison_value_def lpp_integer_term_def)

lemma fresh_machine_trace_support:
 "lpp_no_return_trace_support [] fresh_machine_start fresh_machine_steps = {''X''}"
 by (simp add: fresh_machine_start_def fresh_machine_steps_def)

lemma fresh_machine_trace_rejects_unrenamed_collision:
 "(\<Union>t\<in>set [Var ''X'']. vars_term t) \<inter>
   id ` lpp_no_return_trace_support [] fresh_machine_start fresh_machine_steps \<noteq> {}"
 by (simp add: fresh_machine_trace_support)

lemma fresh_machine_trace_renaming_preserves_caller:
 "(lpc_attach rest (lpc_return_eval LPIVar
     (lpc_no_rename_rows (lpc_no_swap ''X'' ''fresh'') [Var ''X''] fresh_machine_start)),
   lpc_attach rest (lpc_return_eval LPIVar
     (lpc_no_rename_rows (lpc_no_swap ''X'' ''fresh'') [Var ''X''] fresh_machine_end)))
   \<in>(lpp_builtin_source [] (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))\<^sup>+"
 by (rule lpp_no_return_trace_renamed_progress[OF fresh_machine_trace_checked])
   (simp_all add: fresh_machine_trace_support fresh_machine_steps_def fresh_machine_start_def lpc_no_swap_def)

lemma fresh_scope_cannot_capture_caller_cut:
 "\<not> lpc_no_action_scope_safe [LPCCut 7] (LPCNOCase 7)"
 by simp

lemma fresh_scope_accepts_unrelated_caller_cut:
 "lpc_no_action_scope_safe [LPCCut 7] (LPCNOCase 9)"
 by simp

ML \<open>
val checked = [@{thm fresh_machine_trace_checked}, @{thm fresh_machine_trace_support},
 @{thm fresh_machine_trace_rejects_unrenamed_collision}, @{thm fresh_machine_trace_renaming_preserves_caller},
 @{thm fresh_scope_cannot_capture_caller_cut}, @{thm fresh_scope_accepts_unrelated_caller_cut}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted whole-trace freshening controls" else ();
\<close>
end
