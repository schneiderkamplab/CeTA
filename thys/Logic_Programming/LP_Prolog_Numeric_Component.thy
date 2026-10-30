theory LP_Prolog_Numeric_Component
 imports LP_Prolog_Numeric_Calls ITS_Ext.IA4_Instance
begin

definition lpp_check_numeric_component where
  "lpp_check_numeric_component T coordinates locations system_impl D row_receipts child_proof =
    (lpp_check_numeric_calls T coordinates locations (lts_of system_impl) D row_receipts \<and>
      list_all (\<lambda>tr. LTS.source (snd tr)\<in>set (lts_impl.initial system_impl)) (transitions_impl system_impl) \<and>
      isOK (ia4_check_termination system_impl child_proof))"

theorem lpp_check_numeric_component_sound:
  fixes P :: "string lpp_success_clause list" and row_receipts :: "string lpp_numeric_call_receipt list"
  assumes checked: "lpp_check_numeric_component T coordinates locations system_impl D row_receipts child_proof"
    and transfer: "lpp_check_transfer_program T P receipts"
  shows "SN (lpp_observed_calls (set D) P)"
proof (rule lpp_numeric_component_termination[OF _ transfer])
  show "lpp_check_numeric_calls T coordinates locations (lts_of system_impl) D row_receipts"
    using checked by (simp add: lpp_check_numeric_component_def)
  show "LTS.source ` transition_rules (lts_of system_impl) \<subseteq> lts.initial (lts_of system_impl)"
    using checked by (auto simp: lpp_check_numeric_component_def list_all_iff)
  have child: "isOK (ia4_check_termination system_impl child_proof)"
    using checked by (simp add: lpp_check_numeric_component_def)
  show "LPPIntegerLTS.lts_termination (lts_of system_impl)"
    by (rule ia4_check_termination_sound[OF child])
qed

ML \<open>
val checked = [@{thm lpp_check_numeric_component_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted numeric component checker dependency" else ();
\<close>
end
