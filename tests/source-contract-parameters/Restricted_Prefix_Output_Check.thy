theory Restricted_Prefix_Output_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Restricted_Prefix_Output"
begin
lemma free_helper_leaf_positive:
 "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates (1::nat) 2 (Fun 3 [Fun 4 [Fun 5 []]]))
   (Fun (Inr ()) []) (LPIVar (''helper''::string))"
 apply (rule lpp_runtime_leaf_effect_initial)
 unfolding lpp_runtime_structure_def
 by (rule exI[of _ "Var ''helper''"]) simp

lemma partial_caller_is_not_helper_leaf:
 "\<not> lpp_runtime_leaf_effect (lpp_parameter_leaf_templates (1::nat) 2 (Fun 3 [Fun 4 [Fun 5 []]]))
   (Fun (Inr ()) []) (LPIFun 3 [LPIVar (''caller''::string)])"
proof
 assume effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates (1::nat) 2 (Fun 3 [Fun 4 [Fun 5 []]]))
   (Fun (Inr ()) []) (LPIFun 3 [LPIVar (''caller''::string)])"
 have "lpp_caller_output_mode (LPIFun (3::nat) [LPIVar (''caller''::string)])"
  apply (rule lpp_restricted_leaf_output_mode[OF effect])
  apply (rule lpp_parameter_leaf_templates_ground)
  by auto
 then show False by (simp add: lpp_caller_output_mode_def lp_seg_ground.simps)
qed

ML \<open>
val checked = @{thms lpp_restricted_prefix_output_initial lpp_observer_restricted_output_mode
 lpp_observed_output_copy_step free_helper_leaf_positive partial_caller_is_not_helper_leaf};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted restricted prefix output fixture" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-restricted-prefix-output/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "RESTRICTED_PREFIX_OUTPUT_KERNEL_CHECKED";
\<close>
end
