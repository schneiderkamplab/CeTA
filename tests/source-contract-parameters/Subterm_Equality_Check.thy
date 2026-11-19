theory Subterm_Equality_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Subterm_Parameter_Equality_Node"
 "../../thys/Logic_Programming/LP_Prolog_Parameter_Binding_Check_Test"
begin
ML \<open>
val checked = @{thms lpp_checked_observer_subterm_parameter_equality_contract lpp_checked_observer_conditioned_subterm_parameter_equality_contract lpp_observer_subterm_parameter_equality_node_contract parameter_binding_patterns_checked parameter_binding_missing_free_rejected parameter_binding_wrong_coordinate_rejected parameter_binding_compound_selected_rejected parameter_binding_untracked_leaf_rejected parameter_binding_wrong_marker_rejected};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted recursive partial entry" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-subterm-equality/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Arbitrary finite caller output; no helper return or family discharge.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
\<close>
end
