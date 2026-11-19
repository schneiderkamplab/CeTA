theory Partial_Copy_Node_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Observer_Partial_Copy_Node"
begin
ML \<open>
val checked = @{thms lpp_partial_copy_tracked_caller_leaf lpp_attached_tracked_partial_copy_leaf_step
 lpp_checked_observer_partial_copy_contract lpp_observer_partial_copy_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted partial copy node" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-partial-copy-node/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. No output-mode premise. Successor initialization and family descent remain explicit.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
\<close>
end
