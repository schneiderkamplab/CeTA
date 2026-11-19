theory Partial_Copy_Coordinates_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Partial_Copy_Coordinates_Node"
begin
ML \<open>
val checked = @{thms lpp_partial_copy_successor_values lpp_partial_copy_coordinates_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted copy coordinate integration" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-partial-copy-coordinates/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Actual-MGU successor parameter/output facts; remaining successor conditions explicit.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
\<close>
end
