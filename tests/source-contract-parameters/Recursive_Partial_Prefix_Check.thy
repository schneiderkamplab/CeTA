theory Recursive_Partial_Prefix_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Recursive_Partial_Prefix"
begin
ML \<open>
val checked = @{thms lpp_recursive_partial_prefix_initial};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted recursive partial entry" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-recursive-partial-prefix/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Arbitrary finite caller output; no helper return or family discharge.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
\<close>
end
