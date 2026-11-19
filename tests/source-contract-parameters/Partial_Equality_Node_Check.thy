theory Partial_Equality_Node_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Partial_Parameter_Equality_Node"
begin
ML \<open>
val checked = @{thms lpp_attached_subterm_equality_leaf_transport lpp_attached_subterm_equality_leaf_base_step lpp_checked_observer_conditioned_subterm_equality_contract lpp_observer_partial_parameter_equality_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted recursive partial entry" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-partial-equality-node/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Arbitrary finite caller output; no helper return or family discharge.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
\<close>
end
