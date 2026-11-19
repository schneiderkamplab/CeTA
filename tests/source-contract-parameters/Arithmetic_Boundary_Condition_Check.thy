theory Arithmetic_Boundary_Condition_Check
 imports Observer_Output_Rebase_Check
 "../../thys/Logic_Programming/LP_Prolog_Observer_Output_Arithmetic_Node"
begin

definition arithmetic_boundary_conditions where
 "arithmetic_boundary_conditions i eta =
   (if i = (19::nat) then (\<exists>s. eta ''V1'' = LPIFun (LPCUser s) []) else True)"

lemma actual_normalization_scalar_coordinate:
 assumes represented: "lpc_reinterface (\<lambda>env x. env (Inl x))
  ((LPCGoals [LPCUnify left (LPIFun (LPCUser scalar) [])],env)#saved) =
  lpc_return_eval rho [(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],payload)]"
 shows "rho ''V1'' = LPIFun (LPCUser scalar) []"
 using represented by (simp add: lpc_reinterface_def lpc_return_eval_def)

lemma retained_arithmetic_conditioned_node:
 fixes SP :: "string lpp_success_clause list"
 and rest :: "(string lp_cut_symbol,nat) term lp_cut_goal list"
 assumes program: "lp_cut_source_program P"
 and clear: "lpc_rest_scopes rest = {}"
 and compatible: "lpp_stable_integer_operations operation"
 and transfer: "lpp_check_transfer_program T SP receipts"
 and checked: "lpp_check_observed_functor_link T fs fuel P Q nds states contexts Fs functor_contexts
   (nds ! 15) (Fs ! 15) (states ! 15) (contexts ! 15) (functor_contexts ! 15)
   (Var ''V0'') expression [] [Fun f [Fun g [],Var ''V1''],Var ''V1'',Var ''V0''] [] result_var middle"
 and source_shape: "states ! 15 = [(LPCGoals [LPCAtom (Fun (LPCUser ''2:is'') [Var ''V0'',expression])],
   [Fun f [Fun g [],Var ''V1''],Var ''V1'',Var ''V0''])]"
 and target_row: "lpcl_target middle = 19"
 and target_shape: "states ! 19 = [(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],
   [Fun f [Fun g [],Var ''V2''],Var ''V2'',Var ''V0''])]"
 shows "lpp_observer_node_contract names operation SP P lpp_builtin_signature
   (lpp_univ_source_builtin names operation) lpp_univ_source_domain Q nds states contexts Fs functor_contexts
   arithmetic_boundary_conditions (lpp_observer_output_invariant leaf_set specs rest 2 hi) rest returned 15"
 apply (rule lpp_observer_output_arithmetic_node_contract[OF program clear compatible transfer checked source_shape])
 using target_shape target_row
 apply (auto simp: arithmetic_boundary_conditions_def lpc_reinterface_def lpc_return_eval_def)
 by metis

lemma arithmetic_boundary_supplies_equality_entry:
 assumes "arithmetic_boundary_conditions 19 eta"
 shows "equality_scalar_conditions 0 eta"
 using assms by (simp add: arithmetic_boundary_conditions_def equality_scalar_conditions_def)

lemma reject_compound_normalization_coordinate:
 "\<not> arithmetic_boundary_conditions 19
   (\<lambda>_. LPIFun (LPCUser ''compound'') [LPIFun (LPCUser ''scalar'') []])"
 by (simp add: arithmetic_boundary_conditions_def)

ML \<open>
val checked = @{thms actual_normalization_scalar_coordinate retained_arithmetic_conditioned_node
 arithmetic_boundary_supplies_equality_entry reject_compound_normalization_coordinate};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted arithmetic boundary initialization" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-arithmetic-boundary-condition/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "ARITHMETIC_BOUNDARY_CONDITION_KERNEL_CHECKED";
\<close>
end
