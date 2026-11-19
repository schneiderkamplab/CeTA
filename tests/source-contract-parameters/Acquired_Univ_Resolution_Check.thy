theory Acquired_Univ_Resolution_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Acquired_Univ_Resolution"
begin
ML \<open>
val checked = @{thms lpp_actual_acquired_univ_resolution};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted normalized acquisition" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-acquired-univ-resolution/kernel-receipt.txt")
 ("Isabelle checked; no skipped proofs or oracles. Conditional normalized preservation; source evaluation identity derived from actual matching step; complete block and returns remain open.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "ACQUIRED_UNIV_RESOLUTION_RECEIPT_CHECKED";
\<close>
end
