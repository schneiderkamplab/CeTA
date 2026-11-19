theory Recursive_Partial_Entry_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Observer_Recursive_Partial_Node"
 "../../thys/Logic_Programming/LP_Prolog_Split_Prefix_Partial_Entry"
begin
ML \<open>
val checked = @{thms lpp_checked_recursive_partial_entry lpp_observer_recursive_partial_node_contract
 lpp_split_prefix_partial_initial};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted recursive partial entry" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-recursive-partial-entry/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Arbitrary finite caller output; no helper return or family discharge.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
\<close>
end
