theory LP_Prolog_Stable_Mixed_Graph
 imports LP_Prolog_Stable_Backend_Routing
begin

definition lpp_check_stable_mixed_graph where
  "lpp_check_stable_mixed_graph I J fuel P D Q T (SP::string lpp_success_clause list) transfers roots contexts blocks q modes chain_pred
      OD route_rank backends =
    (lpp_check_transfer_program T SP transfers \<and>
      lpp_check_stable_relational_graph fuel P SP D Q T roots contexts blocks q modes chain_pred OD \<and>
      lpp_check_stable_backend_routing I J T SP route_rank OD backends)"

theorem lpp_check_stable_mixed_graph_sound:
  fixes ts :: "(string lp_cut_symbol,string) lp_iterm list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stable_mixed_graph I J fuel P D Q T SP transfers roots contexts blocks q modes chain_pred
      OD route_rank backends"
    and len: "length ts=length modes"
    and ground: "\<forall>(t,b)\<in>set (zip ts modes). b \<longrightarrow> lp_seg_ground t"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
proof -
  have transfer: "lpp_check_transfer_program T SP transfers"
    and graph: "lpp_check_stable_relational_graph fuel P SP D Q T roots contexts blocks q modes chain_pred OD"
    and routed: "lpp_check_stable_backend_routing I J T SP route_rank OD backends"
    using checked by (auto simp: lpp_check_stable_mixed_graph_def)
  have calls: "SN (lpp_stable_observed_calls operation (set OD) SP :: string lpp_success_iatom rel)"
    by (rule lpp_check_stable_backend_routing_sound[OF I J compatible routed transfer])
  have lifted: "SN (inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom ::
      (string lp_cut_symbol,string) lp_iatom rel)"
    by (rule SN_inv_image[OF calls])
  have sn: "SN_on (inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom) {(chain_pred,ts)}"
    by (rule SN_on_subset2[OF subset_UNIV lifted])
  show ?thesis by (rule lpp_stable_relational_graph_root_sound[OF compatible graph transfer sn len ground])
qed

ML \<open>
val checked = [@{thm lpp_check_stable_mixed_graph_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted stable mixed graph dependency" else ();
\<close>
end
