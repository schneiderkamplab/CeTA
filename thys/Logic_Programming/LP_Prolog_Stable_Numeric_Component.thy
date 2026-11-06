theory LP_Prolog_Stable_Numeric_Component
 imports LP_Prolog_Stable_Numeric_Calls
begin

definition lpp_check_stable_numeric_component where
  "lpp_check_stable_numeric_component T coordinates modes locations system_impl D row_receipts child_proof =
    (lpp_check_stable_numeric_calls T coordinates modes locations (lts_of system_impl) D row_receipts \<and>
      list_all (\<lambda>tr. LTS.source (snd tr)\<in>set (lts_impl.initial system_impl)) (transitions_impl system_impl) \<and>
      isOK (ia4_check_termination system_impl child_proof))"

theorem lpp_check_stable_numeric_component_sound:
  fixes P :: "string lpp_success_clause list" and row_receipts :: "string lpp_stable_numeric_call_receipt list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_numeric_component T coordinates modes locations system_impl D row_receipts child_proof"
    and transfer: "lpp_check_transfer_program T P receipts"
  shows "SN (lpp_stable_observed_calls operation (set D) P)"
proof (rule lpp_checked_stable_numeric_calls_SN[OF compatible _ transfer])
  show "lpp_check_stable_numeric_calls T coordinates modes locations (lts_of system_impl) D row_receipts"
    using checked by (simp add: lpp_check_stable_numeric_component_def)
  have entries: "LTS.source ` transition_rules (lts_of system_impl) \<subseteq> lts.initial (lts_of system_impl)"
    using checked by (auto simp: lpp_check_stable_numeric_component_def list_all_iff)
  have child: "isOK (ia4_check_termination system_impl child_proof)"
    using checked by (simp add: lpp_check_stable_numeric_component_def)
  have terminates: "LPPIntegerLTS.lts_termination (lts_of system_impl)"
    by (rule ia4_check_termination_sound[OF child])
  show "SN (LPPIntegerLTS.transition (lts_of system_impl))"
    by (rule lpp_all_numeric_entries_SN[OF entries terminates])
qed

definition lpp_check_stable_projected_numeric_component where
  "lpp_check_stable_projected_numeric_component T positions coordinates modes locations system D row_receipts child =
    (list_all (\<lambda>((h,ps,b,gs),os). lpp_check_call_projection positions h \<and>
      lpp_check_call_projection positions b) D \<and>
      lpp_check_stable_numeric_component T coordinates modes locations system
        (map (lpp_project_observed_triple positions) D) row_receipts child)"

theorem lpp_check_stable_projected_numeric_component_sound:
  fixes P :: "string lpp_success_clause list" and row_receipts :: "string lpp_stable_numeric_call_receipt list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_projected_numeric_component T positions coordinates modes locations system D row_receipts child"
    and transfer: "lpp_check_transfer_program T P receipts"
  shows "SN (lpp_stable_observed_calls operation (set D) P)"
proof -
  have component: "lpp_check_stable_numeric_component T coordinates modes locations system
    (map (lpp_project_observed_triple positions) D) row_receipts child"
    using checked by (simp add: lpp_check_stable_projected_numeric_component_def)
  have projected: "SN (lpp_stable_observed_calls operation (lpp_project_observed_triple positions ` set D) P)"
    using lpp_check_stable_numeric_component_sound[OF compatible component transfer] by simp
  show ?thesis by (rule lpp_stable_projected_calls_SN[OF projected])
qed

ML \<open>
val checked = [@{thm lpp_check_stable_numeric_component_sound},
  @{thm lpp_check_stable_projected_numeric_component_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted stable numeric component dependency" else ();
\<close>
end
