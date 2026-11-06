theory LP_Prolog_Stable_Structural_Child
 imports LP_Prolog_Stable_Structural_Coverage
begin

definition lpp_check_structural_pidp_entries where
  "lpp_check_structural_pidp_entries I J D P entries p d outs fallback dnames pnames marks filters labs proofs =
    list_all (\<lambda>(q,n,positions). check_lp_triple_pidp I J
      (lp_roles_triples p d D) (lp_roles_program p d P)
      outs fallback dnames pnames marks filters (p (LPCUser q)) n positions labs proofs) entries"

theorem lpp_checked_structural_pidp_component:
  fixes P :: "string lpp_success_clause list" and D :: "string lpp_observed_triple list"
    and fallback :: "(string,nat list) lab"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and compatible: "lpp_stable_integer_operations operation"
    and coverage: "lpp_check_structural_entry_coverage T entries D evidence"
    and transfer: "lpp_check_transfer_program T P receipts"
    and subject: "set child_rows=lpp_erase_triples (fst ` set D)"
    and children: "lpp_check_structural_pidp_entries I J child_rows (lpp_erase_success P) entries
      p d outs fallback dnames pnames marks filters labs proofs"
  shows "SN (lpp_stable_observed_calls operation (set D) P :: string lpp_success_iatom rel)"
proof (rule lpp_stable_structural_entries_SN[where entries=entries])
  fix a b
  assume edge: "(a,b)\<in>(lpp_stable_observed_calls operation (set D) P :: string lpp_success_iatom rel)"
  show "lpp_structural_entry_admissible entries b"
    by (rule lpp_checked_structural_coverage_target[OF compatible coverage transfer edge])
next
  fix q n positions
  fix ts :: "(string lp_cut_symbol,string) lp_iterm list"
  assume member: "(q,n,positions)\<in>set entries" and len: "length ts=n"
    and ground: "\<And>i. i\<in>set positions \<Longrightarrow> i<n \<Longrightarrow> lp_seg_ground (ts!i)"
  have child: "check_lp_triple_pidp I J (lp_roles_triples p d child_rows)
      (lp_roles_program p d (lpp_erase_success P)) outs fallback dnames pnames marks filters
      (p (LPCUser q)) n positions labs proofs"
    using children member by (auto simp: lpp_check_structural_pidp_entries_def list_all_iff)
  have result: "SN_on (lp_triple_calls (set child_rows) (lpp_erase_success P)) {(LPCUser q,ts)}"
    by (rule check_lp_triple_pidp_observed_roles_sound[OF I J child len ground])
  show "SN_on (lp_triple_calls (lpp_erase_triples (fst ` set D)) (lpp_erase_success P)) {lpp_lift_iatom (q,ts)}"
    using result by (simp only: subject lpp_lift_iatom_def fst_conv snd_conv)
qed

ML \<open>
val checked = [@{thm lpp_checked_structural_pidp_component}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles checked))
  then error "Untrusted structural child binding" else ();
\<close>
end
