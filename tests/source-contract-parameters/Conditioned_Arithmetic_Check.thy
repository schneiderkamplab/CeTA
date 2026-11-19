theory Conditioned_Arithmetic_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Observer_Conditioned_Arithmetic"
begin
ML \<open>
val checked = @{thms lpp_checked_conditioned_is_invariant_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted recursive partial entry" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-conditioned-arithmetic/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Arbitrary finite caller output; no helper return or family discharge.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
\<close>
end
