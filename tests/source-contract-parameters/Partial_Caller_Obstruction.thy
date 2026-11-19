theory Partial_Caller_Obstruction
 imports "../../thys/Logic_Programming/LP_Prolog_Ground_Caller_Continuation"
begin

text \<open>A nonground compound output can expose a strict compound subterm
of the copied parameter. Copy-or-scalar returns do not bound every caller image
by whole parameters or scalars. Numerals here are distinct test symbols.\<close>

lemma partial_output_outside_mode:
 "\<not> lpp_caller_output_mode (LPIFun (3::nat) [LPIVar (''x''::string)])"
 by (simp add: lpp_caller_output_mode_def lp_seg_ground.simps)

lemma partial_copy_forces_subterm:
 assumes actual: "lpc_mgu_resolve
  (LPIFun (6::nat) [LPIFun 7 [],LPIFun 3 [LPIFun 4 [LPIFun 5 []]],LPIFun 3 [LPIVar ''x'']]) gs
  (Fun 6 [Fun 7 [],Var n,Var n]) bs sigma rho"
 shows "sigma ''x''=LPIFun 4 [LPIFun 5 []]"
proof -
 have eq: "lp_isubst (LPIFun (6::nat) [LPIFun 7 [],LPIFun 3 [LPIFun 4 [LPIFun 5 []]],LPIFun 3 [LPIVar ''x'']]) sigma =
   lp_ieval (Fun 6 [Fun 7 [],Var n,Var n]) rho"
  using actual by (simp only: lpc_mgu_resolve_def)
 have pair: "LPIFun (3::nat) [LPIFun 4 [LPIFun 5 []]]=LPIFun 3 [sigma ''x'']"
  using eq by auto
 show ?thesis using pair by simp
qed

lemma partial_copy_exceeds_whole_parameter_templates:
 assumes actual: "lpc_mgu_resolve
  (LPIFun (6::nat) [LPIFun 7 [],LPIFun 3 [LPIFun 4 [LPIFun 5 []]],LPIFun 3 [LPIVar ''x'']]) gs
  (Fun 6 [Fun 7 [],Var n,Var n]) bs sigma rho"
 shows "\<not> lpp_bounded_images
   (lpp_parameter_leaf_templates 1 2 (Fun 3 [Fun 4 [Fun 5 []]])) sigma {''x''}"
 using partial_copy_forces_subterm[OF actual]
 by (auto simp: lpp_bounded_images_def lpp_parameter_leaf_templates_def)

lemma strict_subterm_repairs_this_image:
 "lpp_bounded_images
   (insert (Fun (4::nat) [Fun 5 []]) (lpp_parameter_leaf_templates 1 2 (Fun 3 [Fun 4 [Fun 5 []]])))
   (\<lambda>_::string. LPIFun 4 [LPIFun 5 []]) {''x''}"
 by (auto simp: lpp_bounded_images_def)

ML \<open>
val checked = @{thms partial_output_outside_mode partial_copy_forces_subterm
 partial_copy_exceeds_whole_parameter_templates strict_subterm_repairs_this_image};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted partial caller obstruction" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-partial-caller-obstruction/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Existing replacement set insufficient for arbitrary nonground compound outputs.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "PARTIAL_CALLER_OBSTRUCTION_KERNEL_CHECKED";
\<close>
end
