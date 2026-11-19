theory Observer_Output_Copy_Node_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Observer_Output_Copy_Node"
begin

lemma combined_empty_goals_positive:
 assumes leaf: "lpp_runtime_leaf_effect A (Fun (Inr ()) []) (LPIVar x)"
 shows "lpp_observer_output_invariant A [(hi,Fun (Inr ()) [])] [] oi hi
  [(LPCGoals [],\<lambda>_. LPIVar x)]"
 using leaf by (simp add: lpp_observer_output_invariant_def lpp_observer_output_alias_def
   lpp_observer_invariant_def lpp_leaf_stack_invariant_def lpc_reinterface_def
   lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)

lemma alias_not_implied_by_leaf_invariant:
 assumes leaf: "lpp_runtime_leaf_effect A (Fun (Inr ()) []) (LPIVar x)"
 and different: "x \<noteq> y"
 defines runtime_def: "runtime \<equiv> [(LPCGoals [],case_sum (\<lambda>_. LPIVar y) (\<lambda>_. LPIVar x))]"
 shows "lpp_observer_invariant A [(hi,Fun (Inr ()) [])] [] runtime \<and>
  \<not> lpp_observer_output_invariant A [(hi,Fun (Inr ()) [])] [] oi hi runtime"
 using leaf different by (simp add: runtime_def lpp_observer_output_invariant_def
   lpp_observer_output_alias_def lpp_observer_invariant_def lpp_leaf_stack_invariant_def
   lpc_reinterface_def lpc_attach_answers_def lpp_finite_execution_def lpp_finite_goals_def)

ML \<open>
val checked = @{thms lpp_observer_output_prefix_initial lpp_observer_output_invariant_scopes
 lpp_checked_observer_output_copy_contract lpp_observer_output_copy_node_contract
 combined_empty_goals_positive alias_not_implied_by_leaf_invariant};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted output copy node fixture" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-observer-output-copy-node/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "OBSERVER_OUTPUT_COPY_NODE_KERNEL_CHECKED";
\<close>
end
