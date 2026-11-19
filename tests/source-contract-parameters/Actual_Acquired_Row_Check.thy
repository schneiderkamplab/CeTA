theory Actual_Acquired_Row_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Acquired_Univ_Row"
begin
ML \<open>
val checked = @{thms lpp_checked_actual_acquired_row};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted normalized acquisition" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-actual-acquired-row/kernel-receipt.txt")
 ("Isabelle checked; no skipped proofs or oracles. Conditional normalized preservation; full row plus actual step supplies common MGU and target valuation; joint block and returns remain open.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "ACTUAL_ACQUIRED_ROW_RECEIPT_CHECKED";
\<close>
end
