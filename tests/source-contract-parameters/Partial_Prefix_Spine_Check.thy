theory Partial_Prefix_Spine_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Partial_Prefix_Return_Spine"
begin
ML \<open>
val checked = @{thms lpp_partial_prefix_actual_return_spine};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted recursive partial entry" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-partial-prefix-spine/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Arbitrary finite caller output; no helper return or family discharge.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
\<close>
end
