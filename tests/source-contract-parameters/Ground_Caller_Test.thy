theory Ground_Caller_Test
 imports "../../thys/Logic_Programming/LP_Prolog_Ground_Caller_Continuation"
  Shared_Caller_Obstruction
begin

lemma repaired_mode_accepts_shared_return:
 "lpp_caller_output_mode (caller_after 4)"
 by (simp add: lpp_caller_output_mode_def caller_after_def caller_before_def caller_binding_def)

lemma nonground_compound_outside_mode:
 "\<not>lpp_caller_output_mode (LPIFun (LPCUser ''f'') [LPIVar (''x'')])"
 by (auto simp: lpp_caller_output_mode_def elim: lp_seg_ground.cases)

lemma bounds_cannot_be_omitted:
 "lpp_caller_output_mode (LPIVar (''x'') :: (string lp_cut_symbol,string) lp_iterm) \<and>
  \<not>lpp_caller_output_mode (lp_isubst (LPIVar ''x'')
   (\<lambda>_. LPIFun (LPCUser ''f'') [LPIVar ''y'']))"
 by (auto simp: lpp_caller_output_mode_def elim: lp_seg_ground.cases)

lemma mismatched_ground_continuation_rejected:
 "\<not>lpc_mgu_resolve
   (LPIFun p [LPIFun nil [],LPIFun (LPCUser ''one'') [],
    LPIFun (LPCUser ''slash'') [LPIFun (LPCUser ''var'') [],LPIFun (LPCUser ''zero'') []]]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 by (rule lpp_ground_caller_copy_mismatch) simp_all

ML \<open>
val checked = @{thms lpp_caller_output_mode_substitute lpp_ground_caller_copy_resolution
 lpp_ground_caller_copy_mismatch lpp_ground_caller_copy_matching lpp_ground_caller_copy_leaf
 repaired_mode_accepts_shared_return nonground_compound_outside_mode bounds_cannot_be_omitted
 mismatched_ground_continuation_rejected};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted ground caller tests" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-ground-caller/kernel-receipt.txt")
 ("Isabelle checked; no skipped proofs or oracles. Local repair; family and Splits remain open.\n" ^
  cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GROUND_CALLER_KERNEL_CHECKED";
\<close>
end
