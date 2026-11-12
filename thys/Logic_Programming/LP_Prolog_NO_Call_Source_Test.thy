theory LP_Prolog_NO_Call_Source_Test
 imports LP_Prolog_NO_Call_Trace_Source LP_Prolog_NO_Call_Check_Test
begin

lemma call_source_query_accepted:
 "lpp_no_call_trace_check_source 10 delayed_program ''recur'' [] [] [] delayed_call [] [] [] []
   [delayed_call] [(delayed_call,delayed_steps)]"
 using delayed_closed_checker_accepts
 by (simp add: lpp_no_call_trace_check_source_def delayed_call_def)

lemma call_source_wrong_query_rejected:
 "\<not> lpp_no_call_trace_check_source 10 delayed_program ''other'' [] [] [] delayed_call [] [] [] []
   [delayed_call] [(delayed_call,delayed_steps)]"
 by (simp add: lpp_no_call_trace_check_source_def delayed_call_def)

lemma call_source_wrong_arity_rejected:
 "\<not> lpp_no_call_trace_check_source 10 delayed_program ''recur'' [True] [] [] delayed_call [] [] [] []
   [delayed_call] [(delayed_call,delayed_steps)]"
 by (simp add: lpp_no_call_trace_check_source_def)

lemma call_source_nonground_mode_rejected:
 "\<not> lpp_no_call_trace_check_source 10 P q [True] [Var ''input''] initial_steps a rest saved reserved vs calls edges"
 by (simp add: lpp_no_call_trace_check_source_def)

lemma call_source_changed_pending_rejected:
 "\<not> lpp_no_call_trace_check_source 10 delayed_program ''recur'' [] [] [] delayed_call [LPCFail] [] [] []
   [delayed_call] [(delayed_call,delayed_steps)]"
 by (simp add: lpp_no_call_trace_check_source_def delayed_call_def)

lemma call_source_changed_saved_rejected:
 "\<not> lpp_no_call_trace_check_source 10 delayed_program ''recur'' [] [] [] delayed_call [] [LPCBarrier 7] [] []
   [delayed_call] [(delayed_call,delayed_steps)]"
 by (simp add: lpp_no_call_trace_check_source_def delayed_call_def)

ML \<open>
val checked = [@{thm call_source_query_accepted}, @{thm call_source_wrong_query_rejected},
 @{thm call_source_wrong_arity_rejected}, @{thm call_source_nonground_mode_rejected},
 @{thm call_source_changed_pending_rejected}, @{thm call_source_changed_saved_rejected}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted original query recurrence controls" else ();
\<close>
end
