theory LP_Prolog_Stable_Computed_Sequence_Return
 imports LP_Prolog_Stable_Computed_Sequence LP_Prolog_Stable_Return_Component
begin

definition lpp_check_computed_sequence_return_component where
  "lpp_check_computed_sequence_return_component T P summaries return_receipts stages positions coordinates modes locations
    weak_system system D row_receipts child =
    (lpp_check_expansion_sequence stages D \<and>
      list_all (\<lambda>((h,ps,b,gs),os). lpp_check_call_projection positions h \<and>
        lpp_check_call_projection positions b) (lpp_expand_observed_sequence stages D) \<and>
      lpp_check_return_numeric_component T P summaries return_receipts coordinates modes locations weak_system system
        (map (lpp_project_observed_triple positions) (lpp_expand_observed_sequence stages D)) row_receipts child)"

theorem lpp_check_computed_sequence_return_component_sound:
  fixes P :: "string lpp_success_clause list" and row_receipts :: "string lpp_return_call_receipt list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_computed_sequence_return_component T P summaries return_receipts stages positions coordinates modes locations
      weak_system system D row_receipts child"
    and transfer: "lpp_check_transfer_program T P receipts"
  shows "SN (lpp_stable_observed_calls operation (set D) P)"
proof -
  have component: "lpp_check_return_numeric_component T P summaries return_receipts coordinates modes locations weak_system system
    (map (lpp_project_observed_triple positions) (lpp_expand_observed_sequence stages D)) row_receipts child"
    using checked by (simp add: lpp_check_computed_sequence_return_component_def)
  have projected: "SN (lpp_stable_observed_calls operation
    (lpp_project_observed_triple positions ` (set (lpp_expand_observed_sequence stages D))) P)"
    using lpp_check_return_numeric_component_sound[OF compatible component transfer] by (simp add: image_image)
  have expanded: "SN (lpp_stable_observed_calls operation (set (lpp_expand_observed_sequence stages D)) P)"
    by (rule lpp_stable_projected_calls_SN[OF projected])
  show ?thesis by (rule lpp_stable_expanded_sequence_SN[OF expanded])
qed

ML \<open>
val checked = [@{thm lpp_check_computed_sequence_return_component_sound}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles checked))
  then error "Untrusted computed sequence return dependency" else ();
\<close>
end
