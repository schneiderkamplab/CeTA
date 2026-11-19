theory Subterm_Ground_Equality_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Subterm_Ground_Equality"
begin
ML \<open>
val checked = @{thms lpp_subterm_ground_equality_images lpp_parameter_subterm_equality_leaf};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted recursive partial entry" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-subterm-ground-equality/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Arbitrary finite caller output; no helper return or family discharge.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
\<close>
end
