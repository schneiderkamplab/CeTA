theory Ground_Output_Images_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Ground_Output_Images"begin

lemma repeated_output_positive:
 fixes sigma :: "string \<Rightarrow> (nat,string) lp_iterm"
 assumes equation: "lp_isubst (LPIFun (3::nat) [LPIVar ''x'',LPIVar ''x'']) sigma=
   lp_ieval (Fun 3 [Fun 4 [Fun 5 []],Fun 4 [Fun 5 []]]) LPIVar"
 shows "lpp_bounded_images (lpp_parameter_subterm_templates 1 2
   (Fun 3 [Fun 4 [Fun 5 []],Fun 4 [Fun 5 []]])) sigma {''x''}"
 using lpp_ground_runtime_output_images[OF _ equation, where f=1 and g=2]
 by (auto intro: lpp_finite_term.intros)

lemma incompatible_repeated_output_negative:
 "\<not>(\<exists>sigma. lp_isubst (LPIFun (3::nat) [LPIVar ''x'',LPIVar ''x'']) sigma=
   LPIFun 3 [LPIFun 4 [],LPIFun 5 []])"
 by auto

ML \<open>
val checked = @{thms lpp_ground_instance_variable_subterm lpp_ground_runtime_output_images
 lpp_partial_caller_copy_output_images lpp_partial_caller_copy_shared_leaf
 repeated_output_positive incompatible_repeated_output_negative};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted output images" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-ground-output-images/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Output support and covered shared caller values; outside-support MGU transport remains open.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
\<close>
end
