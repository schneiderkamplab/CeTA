theory LP_Prolog_Stopped_Case_Mixed_Graph
 imports LP_Prolog_Stopped_Mixed_Graph LP_Prolog_Stable_Success_Case_Rows
begin

fun lpp_success_case_expanded where
 "lpp_success_case_expanded source_rows None = source_rows"
| "lpp_success_case_expanded source_rows (Some receipts) = concat (map2 lpp_success_case_output source_rows receipts)"

fun lpp_check_optional_success_cases where
 "lpp_check_optional_success_cases P source_rows None = True"
| "lpp_check_optional_success_cases P source_rows (Some receipts) =
    list_all2 (lpp_check_success_case_record P) source_rows receipts"

lemma lpp_check_optional_success_cases_sound:
 assumes checked: "lpp_check_optional_success_cases P source_rows receipts"
 shows "lpp_stable_observed_calls operation (set source_rows) P \<subseteq>
   lpp_stable_observed_calls operation (set (lpp_success_case_expanded source_rows receipts)) P"
proof (cases receipts)
 case None
 show ?thesis by (simp add: None)
next
 case (Some items)
 have covered: "list_all2 (lpp_check_success_case_record P) source_rows items"
   using checked by (simp add: Some)
 show ?thesis using lpp_success_case_rows_sound[OF covered]
   by (simp only: Some lpp_success_case_expanded.simps)
qed

definition lpp_check_stopped_case_mixed_graph where
 "lpp_check_stopped_case_mixed_graph I J fuel P D Q T (SP::string lpp_success_clause list) transfers roots contexts blocks q modes chain_pred
      OD cases NOD normalization route_rank backends =
    (lpp_check_optional_success_cases SP OD cases \<and>
      lpp_check_observed_normalization normalization (lpp_success_case_expanded OD cases) NOD \<and>
      lpp_check_transfer_program T SP transfers \<and>
      lpp_check_stopped_graph fuel P SP D Q T roots contexts blocks q modes chain_pred OD \<and>
      lpp_check_field_backend_routing I J T SP route_rank NOD backends)"

theorem lpp_check_stopped_case_mixed_graph_sound:
 fixes ts :: "(string lp_cut_symbol,string) lp_iterm list"
 assumes I: "tp_spec I" and J: "dpp_spec J"
   and compatible: "lpp_stable_integer_operations operation"
   and checked: "lpp_check_stopped_case_mixed_graph I J fuel P D Q T SP transfers roots contexts blocks q modes chain_pred
      OD cases NOD normalization route_rank backends"
   and len: "length ts=length modes"
   and ground: "\<forall>(t,b)\<in>set (zip ts modes). b \<longrightarrow> lp_seg_ground t"
 shows "SN_on (lp_prolog_source P lpp_builtin_signature (lpp_domain_source P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain))
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
proof -
 have cases: "lpp_check_optional_success_cases SP OD cases"
   and enriched_rows: "lpp_check_observed_normalization normalization (lpp_success_case_expanded OD cases) NOD"
   and transfer: "lpp_check_transfer_program T SP transfers"
   and graph: "lpp_check_stopped_graph fuel P SP D Q T roots contexts blocks q modes chain_pred OD"
   and routed: "lpp_check_field_backend_routing I J T SP route_rank NOD backends"
   using checked by (auto simp: lpp_check_stopped_case_mixed_graph_def)
 have normalized_calls: "SN (lpp_stable_observed_calls operation (set NOD) SP :: string lpp_success_iatom rel)"
   by (rule lpp_check_field_backend_routing_sound[OF I J compatible routed transfer])
 have expanded_calls: "SN (lpp_stable_observed_calls operation (set (lpp_success_case_expanded OD cases)) SP :: string lpp_success_iatom rel)"
   by (rule SN_subset[OF normalized_calls lpp_check_observed_normalization_sound[OF enriched_rows]])
 have calls: "SN (lpp_stable_observed_calls operation (set OD) SP :: string lpp_success_iatom rel)"
   by (rule SN_subset[OF expanded_calls lpp_check_optional_success_cases_sound[OF cases]])
 have lifted: "SN (inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom ::
      (string lp_cut_symbol,string) lp_iatom rel)"
   by (rule SN_inv_image[OF calls])
 have sn: "SN_on (inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom) {(chain_pred,ts)}"
   by (rule SN_on_subset2[OF subset_UNIV lifted])
 show ?thesis by (rule lpp_stopped_graph_root_sound[OF compatible graph transfer sn len ground])
qed

ML \<open>
val checked = [@{thm lpp_check_stopped_case_mixed_graph_sound}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles checked))
 then error "Untrusted helper-case source assembly" else ();
\<close>
end
