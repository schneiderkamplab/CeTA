theory Equality_Output_Preservation_Check
 imports Equality_Output_Module_Check
begin

lemma equality_caller_coverage_positive:
 "lpp_check_attached_leaf_slots [0::nat] [LPCUnify (Var 0) (Var 1)]"
 by (simp add: lpp_check_attached_leaf_slots_def lpp_leaf_goals_variables_correct)

lemma equality_missing_caller_coverage_rejected:
 "\<not> lpp_check_attached_leaf_slots [0::nat] [LPCUnify (Var 1) (Var 1)]"
 by (simp add: lpp_check_attached_leaf_slots_def lpp_leaf_goals_variables_correct)

ML \<open>
val checked = @{thms lpp_observer_output_equality_child_invariant
 lpp_observer_output_equality_preservation lpp_observer_output_scalar_equality_preservation
 lpp_checked_observer_output_equality_contract retained_equality_output_module_contract
 equality_caller_coverage_positive equality_missing_caller_coverage_rejected};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted equality preservation integration" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-output-equality-preservation/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Caller continuation and global family assembly remain open.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "OUTPUT_EQUALITY_PRESERVATION_KERNEL_CHECKED";
\<close>
end
