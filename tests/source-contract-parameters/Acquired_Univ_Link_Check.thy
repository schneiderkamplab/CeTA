theory Acquired_Univ_Link_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Acquired_Univ_Link"
begin
ML \<open>
val checked = @{thms lpp_acquired_univ_link_correspondence};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted normalized acquisition" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-acquired-univ-link/kernel-receipt.txt")
 ("Isabelle checked; no skipped proofs or oracles. Conditional normalized preservation; complete target coordinate and interface correspondence derived from checked link; source evaluation identity remains explicit.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "ACQUIRED_UNIV_LINK_RECEIPT_CHECKED";
\<close>
end
