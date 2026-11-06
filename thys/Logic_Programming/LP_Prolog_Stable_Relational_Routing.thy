theory LP_Prolog_Stable_Relational_Routing
 imports LP_Prolog_Stable_Relational_Graph LP_Prolog_Stable_Routing_Coverage
begin

theorem lpp_stable_relational_routed_graph_sound:
  fixes ts :: "(string lp_cut_symbol,string) lp_iterm list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and graph: "lpp_check_stable_relational_graph fuel P SP D Q T roots contexts blocks q modes chain_pred OD"
    and transfer: "lpp_check_transfer_program T SP transfers"
    and routing: "lpp_check_stable_finite_routing route_rank component_count OD"
    and components: "\<And>n. n<component_count \<Longrightarrow>
      SN (lpp_stable_observed_calls operation (lpp_stable_rank_rows route_rank n (set OD)) SP :: string lpp_success_iatom rel)"
    and len: "length ts=length modes"
    and ground: "\<forall>(t,b)\<in>set (zip ts modes). b \<longrightarrow> lp_seg_ground t"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
proof -
  have calls: "SN (lpp_stable_observed_calls operation (set OD) SP :: string lpp_success_iatom rel)"
    by (rule lpp_stable_finite_routed_calls_SN[OF routing components])
  have lifted: "SN (inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom ::
      (string lp_cut_symbol,string) lp_iatom rel)"
    by (rule SN_inv_image[OF calls])
  have sn: "SN_on (inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom) {(chain_pred,ts)}"
    by (rule SN_on_subset2[OF subset_UNIV lifted])
  show ?thesis by (rule lpp_stable_relational_graph_root_sound[OF compatible graph transfer sn len ground])
qed

ML \<open>
val checked = [@{thm lpp_stable_relational_routed_graph_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted relational routed graph" else ();
\<close>
end
