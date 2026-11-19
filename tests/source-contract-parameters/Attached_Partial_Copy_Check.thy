theory Attached_Partial_Copy_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Attached_Partial_Copy"
begin
ML \<open>
val checked = @{thms lpp_partial_copy_continuation_images lpp_partial_copy_runtime_continuation_images
 lpp_partial_copy_caller_leaf lpp_attached_partial_caller_copy_leaf_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted attached partial copy" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-attached-partial-copy/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Full covered caller continuation; finite arbitrary output. Node and family integration remain open.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
\<close>
end
