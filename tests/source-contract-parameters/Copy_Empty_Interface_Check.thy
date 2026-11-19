theory Copy_Empty_Interface_Check
 imports Global_Copy_Return_Check
begin

text \<open>The cut module has an empty helper payload. Replacing the helper
interface with that payload destroys an output alias for any non-truth copied
parameter. Caller state itself is unchanged. This is an assembly obstruction,
not a rejection of the source program or its termination.\<close>

lemma empty_helper_payload_value:
 "lpc_return_env [] eta i = LPIFun LPCTruth []"
 by (simp add: lpc_return_env_def)

lemma empty_helper_rebase_alias_iff:
 "lpp_observer_output_alias oi hi
   [(LPCGoals goals,case_sum (lpc_return_env [] eta) caller_env)] =
  (caller_env hi = LPIFun LPCTruth [])"
 by (simp add: lpp_observer_output_alias_def lpc_return_env_def eq_commute)

lemma copied_parameter_empty_interface_obstruction:
 assumes copied: "caller_env hi = parameter"
 and nontruth: "parameter \<noteq> LPIFun LPCTruth []"
 shows "\<not> lpp_observer_output_invariant A specs rest oi hi
   [(LPCGoals goals,case_sum (lpc_return_env [] eta) caller_env)]"
 using copied nontruth
 by (simp add: lpp_observer_output_invariant_def empty_helper_rebase_alias_iff)

lemma empty_helper_rebase_keeps_caller:
 "lpc_reinterface (\<lambda>e x. e (Inr x))
   [(LPCGoals goals,case_sum (lpc_return_env [] eta) caller_env)] =
  [(LPCGoals goals,caller_env)]"
 by (simp add: lpc_reinterface_def)

lemma compound_copy_obstruction:
 "\<not> lpp_observer_output_invariant A specs rest oi hi
   [(LPCGoals goals,case_sum (lpc_return_env [] eta)
     (\<lambda>_. LPIFun (LPCUser ''f'') [LPIFun (LPCUser ''a'') []]))]"
 by (rule copied_parameter_empty_interface_obstruction[OF refl]) simp

lemma truth_alias_positive_control:
 "lpp_observer_output_alias oi hi
   [(LPCGoals goals,case_sum (lpc_return_env [] eta) (\<lambda>_. LPIFun LPCTruth []))]"
 by (simp add: empty_helper_rebase_alias_iff)

ML \<open>
val checked = @{thms empty_helper_payload_value empty_helper_rebase_alias_iff
 copied_parameter_empty_interface_obstruction empty_helper_rebase_keeps_caller
 compound_copy_obstruction truth_alias_positive_control};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted empty interface obstruction" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-copy-empty-interface/kernel-receipt.txt")
 ("Kernel checked; no skips or oracles. Current helper-output alias does not survive empty-payload rebasing.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "COPY_EMPTY_INTERFACE_KERNEL_CHECKED";
\<close>
end
