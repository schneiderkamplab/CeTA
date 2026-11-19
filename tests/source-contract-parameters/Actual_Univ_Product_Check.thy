theory Actual_Univ_Product_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Acquired_Actual_Univ_Product"
begin
ML \<open>
val checked = @{thms lpp_attached_univ_actual_path lpp_acquired_actual_univ_product};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted actual univ product" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-actual-univ-product/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Coverage and representation remain premises.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
\<close>
end
