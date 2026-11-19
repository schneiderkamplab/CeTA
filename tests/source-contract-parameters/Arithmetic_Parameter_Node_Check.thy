theory Arithmetic_Parameter_Node_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Arithmetic_Target_Payload"
begin
ML \<open>
val checked = @{thms lpp_observer_arithmetic_parameter_node_contract lpp_arithmetic_target_payload_parameter};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted recursive partial entry" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-arithmetic-parameter-node/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Arbitrary finite caller output; no helper return or family discharge.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
\<close>
end
