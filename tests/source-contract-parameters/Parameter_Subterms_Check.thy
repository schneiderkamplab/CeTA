theory Parameter_Subterms_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Parameter_Subterms"
begin

lemma previous_counterexample_admitted:
 "Fun (4::nat) [Fun 5 []]\<in>lpp_parameter_subterm_templates 1 2 (Fun 3 [Fun 4 [Fun 5 []]])"
 unfolding lpp_parameter_subterm_templates_def
 apply (rule CollectI, rule bexI[of _ "Fun 3 [Fun 4 [Fun 5 []]]"])
 apply (rule lpp_finite_template_subterm.child[where v="Fun 4 [Fun 5 []]"])
 apply simp
 apply (rule lpp_finite_template_subterm.root)
 by (simp add: lpp_parameter_leaf_templates_def)

lemma variable_replacement_rejected:
 "(Var ''x'' :: (nat,string) term)\<notin>lpp_parameter_subterm_templates 1 2 (Fun 3 [Fun 4 [Fun 5 []]])"
 using lpp_parameter_subterm_templates_ground[of "Fun (3::nat) [Fun 4 [Fun 5 []]]" "Var ''x''" 1 2] by auto

lemma growing_replacement_rejected:
 "(Fun 8 (replicate 10 (Fun 5 [])) :: (nat,string) term)\<notin>
   lpp_parameter_subterm_templates 1 2 (Fun 3 [Fun 4 [Fun 5 []]])"
 using lpp_parameter_subterm_templates_budget[of "Fun (3::nat) [Fun 4 [Fun 5 []]]" "Fun 8 (replicate 10 (Fun 5 [])) :: (nat,string) term" 1 2]
 by (auto simp: lpp_parameter_leaf_budget_def numeral_eq_Suc)

ML \<open>
val checked = @{thms lpp_parameter_subterm_templates_ground lpp_parameter_subterm_templates_budget
 lpp_parameter_return_subterm_templates lpp_parameter_subterm_leaf_composition
 previous_counterexample_admitted variable_replacement_rejected growing_replacement_rejected};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted subterm controls" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-parameter-subterms/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Actual image and family integration remain open.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
\<close>
end
