theory LP_Prolog_Stable_Return_Component
 imports LP_Prolog_Stable_Return_Calls LP_Prolog_Stable_Computed_Projection
begin

definition lpp_check_return_numeric_component where
  "lpp_check_return_numeric_component T P summaries return_receipts coordinates modes locations
    weak_system system_impl D row_receipts child_proof =
    (lpp_check_magnitude_program summaries P return_receipts \<and>
      lpp_check_return_calls T summaries coordinates modes locations weak_system (lts_of system_impl) D row_receipts \<and>
      list_all (\<lambda>tr. LTS.source (snd tr)\<in>set (lts_impl.initial system_impl)) (transitions_impl system_impl) \<and>
      isOK (ia4_check_termination system_impl child_proof))"

theorem lpp_check_return_numeric_component_sound:
  fixes P :: "string lpp_success_clause list" and row_receipts :: "string lpp_return_call_receipt list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_return_numeric_component T P summaries return_receipts coordinates modes locations
      weak_system system_impl D row_receipts child_proof"
    and transfer: "lpp_check_transfer_program T P receipts"
  shows "SN (lpp_stable_observed_calls operation (set D) P)"
proof (rule lpp_checked_return_calls_SN[OF compatible _ transfer])
  show "lpp_check_return_calls T summaries coordinates modes locations weak_system (lts_of system_impl) D row_receipts"
    using checked by (simp add: lpp_check_return_numeric_component_def)
  show "lpp_check_magnitude_program summaries P return_receipts"
    using checked by (simp add: lpp_check_return_numeric_component_def)
  have entries: "LTS.source ` transition_rules (lts_of system_impl) \<subseteq> lts.initial (lts_of system_impl)"
    using checked by (auto simp: lpp_check_return_numeric_component_def list_all_iff)
  have child: "isOK (ia4_check_termination system_impl child_proof)"
    using checked by (simp add: lpp_check_return_numeric_component_def)
  have terminates: "LPPIntegerLTS.lts_termination (lts_of system_impl)"
    by (rule ia4_check_termination_sound[OF child])
  show "SN (LPPIntegerLTS.transition (lts_of system_impl))"
    by (rule lpp_all_numeric_entries_SN[OF entries terminates])
qed

definition lpp_check_computed_return_component where
  "lpp_check_computed_return_component T P summaries return_receipts expressions positions coordinates modes locations
    weak_system system D row_receipts child =
    (list_all (\<lambda>((h,ps,b,gs),os). lpp_check_argument_expansion expressions h \<and>
      lpp_check_argument_expansion expressions b) D \<and>
      list_all (\<lambda>((h,ps,b,gs),os). lpp_check_call_projection positions h \<and>
        lpp_check_call_projection positions b) (map (lpp_expand_observed_triple expressions) D) \<and>
      lpp_check_return_numeric_component T P summaries return_receipts coordinates modes locations weak_system system
        (map (lpp_project_observed_triple positions o lpp_expand_observed_triple expressions) D) row_receipts child)"

theorem lpp_check_computed_return_component_sound:
  fixes P :: "string lpp_success_clause list" and row_receipts :: "string lpp_return_call_receipt list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_computed_return_component T P summaries return_receipts expressions positions coordinates modes locations
      weak_system system D row_receipts child"
    and transfer: "lpp_check_transfer_program T P receipts"
  shows "SN (lpp_stable_observed_calls operation (set D) P)"
proof -
  have component: "lpp_check_return_numeric_component T P summaries return_receipts coordinates modes locations weak_system system
    (map (lpp_project_observed_triple positions o lpp_expand_observed_triple expressions) D) row_receipts child"
    using checked by (simp add: lpp_check_computed_return_component_def)
  have projected: "SN (lpp_stable_observed_calls operation
    (lpp_project_observed_triple positions ` (lpp_expand_observed_triple expressions ` set D)) P)"
    using lpp_check_return_numeric_component_sound[OF compatible component transfer] by (simp add: image_image)
  have expanded: "SN (lpp_stable_observed_calls operation (lpp_expand_observed_triple expressions ` set D) P)"
    by (rule lpp_stable_projected_calls_SN[OF projected])
  show ?thesis by (rule lpp_stable_expanded_calls_SN[OF expanded])
qed

ML \<open>
val checked = [@{thm lpp_check_return_numeric_component_sound}, @{thm lpp_check_computed_return_component_sound}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles checked))
  then error "Untrusted return component dependency" else ();
\<close>
end
