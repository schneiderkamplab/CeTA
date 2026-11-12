theory LP_Prolog_NO_Call_Trace_Test
 imports LP_Prolog_NO_Call_Trace_Recurrence
begin

definition delayed_call :: "(string lp_cut_symbol,string) term" where
 "delayed_call = Fun (LPCUser ''recur'') []"
definition delayed_program where
 "delayed_program = [(delayed_call,[LPCAtom delayed_call,LPCTrue])]"
definition delayed_start where
 "delayed_start = [(LPCGoals [LPCAtom delayed_call],[])]"
definition delayed_case where
 "delayed_case = [(LPCClause [LPCAtom delayed_call] 0 7,[]),(LPCBarrier 7,[])]"
definition delayed_end where
 "delayed_end = [(LPCGoals [LPCAtom delayed_call,LPCTrue],[]),(LPCBarrier 7,[])]"
definition delayed_steps where
 "delayed_steps = [
  (LPPMBase (LPPGIBase (LPPIOrdinary (LPPNOOrdinary (LPCNOCase 7)))),delayed_case),
  (LPPMBase (LPPGIBase (LPPIOrdinary (LPPNOOrdinary (LPCNOResolve 1 [] [])))),delayed_end)]"

lemma delayed_trace_checked:
 "lpp_no_return_trace 10 delayed_program [] delayed_start delayed_steps delayed_end"
 by (simp add: delayed_program_def delayed_call_def delayed_start_def delayed_case_def
   delayed_end_def delayed_steps_def lpp_no_return_ordinary_step_def lp_cut_fresh_def lp_cut_slice_def;
   code_simp)

lemma delayed_boundaries_checked:
 "lpp_no_return_boundaries delayed_start delayed_steps"
 by (simp add: delayed_start_def delayed_steps_def delayed_case_def delayed_end_def
   lpp_no_return_owned_boundary_def lpc_no_rows_have_frame_def)

lemma delayed_call_nonterminating:
 "\<not> SN_on (lpp_builtin_source delayed_program
   (lpp_stable_source_builtin (lpp_binary64_profile_operation fallback)))
   {lp_cut_state_eval [LPCGoals [LPCAtom delayed_call]] LPIVar}"
proof (rule lpp_no_closed_call_traces_nonterminating[where A="{delayed_call}" and vs="[]" and fuel=10 and reserved="[]"])
 show "delayed_call\<in>{delayed_call}" by simp
 show "distinct ([]::string list)" by simp
 show "\<forall>b\<in>{delayed_call}. vars_term b \<subseteq> set ([]::string list)"
   by (simp add: delayed_call_def)
 show "lp_cut_source_program delayed_program"
   by (simp add: delayed_program_def lp_cut_source_program_def)
 fix b assume "b\<in>{delayed_call}"
 then have b: "b=delayed_call" by simp
 show "\<exists>c\<in>{delayed_call}. \<exists>steps pending payload saved.
   lpp_no_return_trace 10 delayed_program [] [(LPCGoals [LPCAtom b],map Var [])] steps
     ((LPCGoals (LPCAtom c#pending),payload)#saved) \<and>
   lpp_no_return_boundaries [(LPCGoals [LPCAtom b],map Var [])] steps \<and> steps\<noteq>[]"
   using delayed_trace_checked delayed_boundaries_checked
   by (intro bexI[of _ delayed_call] exI[of _ delayed_steps] exI[of _ "[LPCTrue]"]
      exI[of _ "[]"] exI[of _ "[(LPCBarrier 7,[])]"])
     (simp_all add: b delayed_start_def delayed_end_def delayed_steps_def)
qed

lemma delayed_missing_transition_rejected:
 "\<not> lpp_no_return_trace 10 delayed_program [] delayed_start (tl delayed_steps) delayed_end"
 by (simp add: delayed_program_def delayed_call_def delayed_start_def delayed_case_def
   delayed_end_def delayed_steps_def lpp_no_return_ordinary_step_def lp_cut_fresh_def lp_cut_slice_def;
   code_simp)

lemma delayed_empty_successor_rejected:
 "\<not> lpp_no_return_owned_boundary delayed_start []"
 by (simp add: lpp_no_return_owned_boundary_def)

lemma delayed_unowned_cut_rejected:
 "\<not> lpp_no_return_owned_boundary [(LPCGoals [LPCCut 7],[])] delayed_end"
 by (simp add: lpp_no_return_owned_boundary_def)

ML \<open>
val checked = [@{thm delayed_trace_checked}, @{thm delayed_boundaries_checked},
 @{thm delayed_call_nonterminating}, @{thm delayed_missing_transition_rejected},
 @{thm delayed_empty_successor_rejected}, @{thm delayed_unowned_cut_rejected}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted delayed call recurrence controls" else ();
\<close>
end
