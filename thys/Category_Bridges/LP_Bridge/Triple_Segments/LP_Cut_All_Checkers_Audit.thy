theory LP_Cut_All_Checkers_Audit
  imports
    Category_LP_Bridge.LP_Cut_Checker_Bridge
    Category_LP_Cut_Checker_Bridge.LP_Cut_Domain_Checker
    Category_LP_Cut_Composition_Bridge.LP_Cut_Domain_Return_Composed_Checker
    Category_LP_Cut_Composition_Bridge.LP_Cut_Domain_Return_Composed_Triples
    Category_LP_Cut_Family_Bridges.LP_Cut_Constructor_Category_Bridge
    Category_LP_Cut_Free_Segment_Bridge.LP_Cut_Domain_SEG_Free_Checker
    Category_LP_Cut_MGU_Bridge.LP_Cut_Domain_Precise_Checker
    Category_LP_Cut_NO_Bridge.LP_Cut_Domain_NO_Checker
    Category_LP_Cut_Nested_Bridge.LP_Cut_Domain_Return_Nested_Checker
    Category_LP_Cut_Nested_Bridge.LP_Cut_Domain_Return_Nested_Triples
    Category_LP_Cut_Projected_Bridge.LP_Cut_Domain_Projected_Checker
    Category_LP_Cut_Projected_Segment_Bridge.LP_Cut_Domain_SEG_Projected_Checker
    Category_LP_Cut_Return_Bridge.LP_Cut_Domain_Return_Checker
    Category_LP_Cut_Return_Bridge.LP_Cut_Domain_Return_Module_Checker
    Category_LP_Cut_Return_Bridge.LP_Cut_Domain_Return_Module_Triples
    Category_LP_Cut_Return_Bridge.LP_Cut_Domain_Return_Triples
    Category_LP_Cut_Segment_Bridge.LP_Cut_Domain_SEG_Checker
    LP_Cut_Domain_SEG_Triple_Checker
begin

text \<open>Every LP-with-cut acceptance branch in the unified dispatcher has
three separate canonical soundness corollaries. This audit includes all of them;
source-file correspondence and runtime domain selection are separate obligations.\<close>

ML \<open>
  val results = @{thms lp_cut_constructor_finite_yes lp_cut_constructor_rational_yes lp_cut_constructor_infinite_yes lp_cut_mgu_finite_yes lp_cut_mgu_rational_yes lp_cut_mgu_infinite_yes lp_cut_source_finite_no lp_cut_source_rational_no lp_cut_source_infinite_no lp_cut_projected_finite_yes lp_cut_projected_rational_yes lp_cut_projected_infinite_yes lp_cut_return_composed_finite_yes lp_cut_return_composed_rational_yes lp_cut_return_composed_infinite_yes lp_cut_return_composed_triples_finite_yes lp_cut_return_composed_triples_rational_yes lp_cut_return_composed_triples_infinite_yes lp_cut_return_finite_yes lp_cut_return_rational_yes lp_cut_return_infinite_yes lp_cut_return_module_finite_yes lp_cut_return_module_rational_yes lp_cut_return_module_infinite_yes lp_cut_return_module_triples_finite_yes lp_cut_return_module_triples_rational_yes lp_cut_return_module_triples_infinite_yes lp_cut_return_nested_finite_yes lp_cut_return_nested_rational_yes lp_cut_return_nested_infinite_yes lp_cut_return_nested_triples_finite_yes lp_cut_return_nested_triples_rational_yes lp_cut_return_nested_triples_infinite_yes lp_cut_return_triples_finite_yes lp_cut_return_triples_rational_yes lp_cut_return_triples_infinite_yes lp_cut_seg_finite_yes lp_cut_seg_rational_yes lp_cut_seg_infinite_yes lp_cut_seg_free_finite_yes lp_cut_seg_free_rational_yes lp_cut_seg_free_infinite_yes lp_cut_seg_projected_finite_yes lp_cut_seg_projected_rational_yes lp_cut_seg_projected_infinite_yes lp_cut_seg_triples_finite_yes lp_cut_seg_triples_rational_yes lp_cut_seg_triples_infinite_yes lp_cut_table_finite_yes lp_cut_table_rational_yes lp_cut_table_infinite_yes}
  val _ = if Thm_Deps.has_skip_proof results then error "Cut dispatcher: admitted proof" else ()
  val names = Thm_Deps.all_oracles results |> map (fn ((name, _), _) => name) |> distinct (op =)
  val unexpected = subtract (op =) ["Regexp_Method.check_eqv", "Types_To_Sets.cancel_type_definition"] names
  val _ = if null unexpected then () else error ("Cut dispatcher: unexpected oracles: " ^ commas unexpected)
  val _ = warning ("Cut dispatcher: audited 51 canonical corollaries; oracle dependencies: " ^ commas names)
\<close>
end
