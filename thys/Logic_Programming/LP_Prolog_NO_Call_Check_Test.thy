theory LP_Prolog_NO_Call_Check_Test
 imports LP_Prolog_NO_Call_Trace_Check LP_Prolog_NO_Call_Trace_Test
begin

lemma delayed_edge_checked:
 "lpp_no_call_trace_edge 10 delayed_program [] [] [delayed_call] delayed_call delayed_steps"
 using delayed_trace_checked delayed_boundaries_checked
 by (simp add: lpp_no_call_trace_edge_def delayed_start_def delayed_steps_def delayed_end_def)

lemma delayed_closed_checker_accepts:
 "lpp_no_call_trace_check 10 delayed_program [] [] [delayed_call]
   [(delayed_call,delayed_steps)] delayed_call"
 using delayed_edge_checked
 by (simp add: lpp_no_call_trace_check_def delayed_call_def delayed_program_def lp_cut_source_program_def)

lemma delayed_missing_edge_rejected:
 "\<not> lpp_no_call_trace_check 10 delayed_program [] [] [delayed_call] [] delayed_call"
 by (simp add: lpp_no_call_trace_check_def)

lemma delayed_empty_trace_rejected:
 "\<not> lpp_no_call_trace_edge 10 delayed_program [] [] [delayed_call] delayed_call []"
 by (simp add: lpp_no_call_trace_edge_def)

lemma delayed_missing_target_rejected:
 "\<not> lpp_no_call_trace_edge 10 delayed_program [] [] [] delayed_call delayed_steps"
 by (simp add: lpp_no_call_trace_edge_def delayed_steps_def delayed_end_def)

lemma delayed_uncovered_interface_rejected:
 "\<not> lpp_no_call_trace_check 10 P [] [] [Var ''live''] edges (Var ''live'')"
 by (simp add: lpp_no_call_trace_check_def)

ML \<open>
val checked = [@{thm delayed_edge_checked}, @{thm delayed_closed_checker_accepts},
 @{thm delayed_missing_edge_rejected}, @{thm delayed_empty_trace_rejected},
 @{thm delayed_missing_target_rejected}, @{thm delayed_uncovered_interface_rejected}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite call checker controls" else ();
\<close>
end
