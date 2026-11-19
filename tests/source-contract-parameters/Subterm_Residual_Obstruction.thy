theory Subterm_Residual_Obstruction
 imports "../../thys/Logic_Programming/LP_Prolog_Parameter_Leaf_Program"
   "../../thys/Logic_Programming/LP_Prolog_Parameter_Subterms"
begin

text \<open>The widened invariant cannot use the existing replacement-coverage
interface unchanged. This refutes coverage by its four replacement patterns,
not every possible simulation using the full retained residual.\<close>

lemma exposed_subterm_allowed:
 "Fun (4::nat) [Fun 5 []] \<in>
   lpp_parameter_subterm_templates 1 2 (Fun 3 [Fun 4 [Fun 5 []]])"
 unfolding lpp_parameter_subterm_templates_def
 by (auto simp: lpp_parameter_leaf_templates_def
   intro: lpp_finite_template_subterm.intros)

lemma exposed_subterm_not_covered:
 "\<not> (\<exists>pattern nu.
   pattern \<in> set (lpp_parameter_leaf_patterns (1::nat) 2) \<and>
   nu 0 = lp_ieval (lpp_reify_structure
     (lpp_structure_template (Fun 3 [Fun 4 [Fun 5 []]]))) LPIVar \<and>
   lp_ieval pattern nu = lp_ieval (lpp_reify_structure
     (lpp_structure_template (Fun 4 [Fun 5 []]))) LPIVar)"
 by (auto simp: lpp_parameter_leaf_patterns_def lpp_leaf_marker_pattern_def
   lpp_leaf_atomic_pattern_def)

lemma whole_parameter_still_covered:
 "\<exists>pattern nu.
   pattern \<in> set (lpp_parameter_leaf_patterns (1::nat) 2) \<and>
   nu 0 = lp_ieval (lpp_reify_structure
     (lpp_structure_template (Fun 3 [Fun 4 [Fun 5 []]]))) LPIVar \<and>
   lp_ieval pattern nu = lp_ieval (lpp_reify_structure
     (lpp_structure_template (Fun 3 [Fun 4 [Fun 5 []]]))) LPIVar"
 by (rule exI[of _ "Var 0"], rule exI[of _ "\<lambda>_. lp_ieval
   (lpp_reify_structure (lpp_structure_template (Fun 3 [Fun 4 [Fun 5 []]]))) LPIVar"])
   (simp add: lpp_parameter_leaf_patterns_def)

ML \<open>
val checked = @{thms exposed_subterm_allowed exposed_subterm_not_covered whole_parameter_still_covered};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted subterm residual obstruction" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-subterm-residual-obstruction/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "SUBTERM_RESIDUAL_OBSTRUCTION_KERNEL_CHECKED";
\<close>
end
