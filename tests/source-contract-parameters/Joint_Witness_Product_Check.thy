theory Joint_Witness_Product_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Acquired_Joint_Witness_Product"
begin
ML \<open>
val checked = @{thms lpp_acquired_joint_constructor_product lpp_acquired_joint_witness_product};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted joint witness product" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-joint-witness-product/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Constructor and variable input cases.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
\<close>
end
