theory Observer_Output_Arithmetic_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Observer_Output_Arithmetic_Node"
   "../../thys/Logic_Programming/LP_Prolog_Observer_Output_Scalar_Equality_Node"
begin

lemma scalar_subterms_covered:
 assumes sub: "lpp_finite_template_subterm u (Fun (h::nat) [])"
 shows "u \<in> lpp_parameter_leaf_templates f g c"
 using sub by (cases rule: lpp_finite_template_subterm.cases)
   (auto simp: lpp_parameter_leaf_templates_def)

lemma compound_parameter_does_not_supply_closure:
 "\<exists>u. lpp_finite_template_subterm u (Fun (3::nat) [Fun 4 [Fun 5 []]]) \<and>
   u \<notin> lpp_parameter_leaf_templates 1 2 (Fun 3 [Fun 4 [Fun 5 []]])"
 apply (rule exI[of _ "Fun 4 [Fun 5 []]"])
 by (auto simp: lpp_parameter_leaf_templates_def intro: lpp_finite_template_subterm.intros)

ML \<open>
val checked = @{thms lpp_checked_conditioned_is_output_contract
 lpp_observer_output_arithmetic_node_contract lpp_checked_observer_output_equality_contract
 lpp_checked_observer_output_scalar_equality_contract lpp_observer_output_scalar_equality_node_contract
 scalar_subterms_covered compound_parameter_does_not_supply_closure};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted arithmetic/output equality fixture" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-observer-output-arithmetic/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "OBSERVER_OUTPUT_ARITHMETIC_KERNEL_CHECKED";
\<close>
end
