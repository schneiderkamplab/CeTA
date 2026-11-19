theory Checked_Acquired_Block_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Checked_Acquired_Block"
begin
ML \<open>
val checked = @{thms lpp_checked_acquired_block};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted acquired block" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-checked-acquired-block/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Actual resolution and actual builtin composed; incoming invariant and row checks remain premises.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
\<close>
end
