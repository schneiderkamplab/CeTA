theory Actual_Witness_Product_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Acquired_Actual_Witness_Product"
   "../../thys/Logic_Programming/LP_Prolog_Acquired_Univ_Joint_Row"
begin
ML \<open>
val checked = @{thms lpp_acquired_actual_witness_product lpp_checked_attached_acquired_row};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted actual witness product" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-actual-witness-product/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Incoming conditions and row checks remain explicit.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
\<close>
end
