theory LP_Cut_Domain_Return_Split_Check
  imports LP_Cut_Domain_Return_Split_Shape
begin

context cut_runtime_domain
begin

theorem precise_return_split_checked_contract:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_check_return_split fuel P Q nd original returned arity
      bindings indices pre rest interface prefix_module prefix_link vs continuation_module continuation_link"
    and program: "lp_cut_source_program P"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and sn: "SN_on (lp_ild Q) {[(lpcn_pred nd,map eta (lpcn_vars nd))]}"
  shows "precise_return_contract P (lpc_return_eval eta original) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof -
  let ?t = "[(lpcn_pred nd,map eta (lpcn_vars nd))]"
  let ?gs = "map (lp_cut_map (map_term id (lpc_return_route bindings))) rest"
  let ?pre_ret = "\<lambda>rho. [(lpcrm_returned prefix_module,map rho [0..<length vs])]"
  let ?cont_ret = "\<lambda>rho. [(lpcrm_returned continuation_module,map rho [0..<length vs])]"
  have shape: "lpc_check_return_split_shape bindings indices pre rest interface original"
    and arity: "length indices=arity"
    and distinct: "distinct vs"
    and indexed: "lpc_return_indexed_goals (length vs) ?gs"
    and projection: "lpc_check_return_projection_edge Q vs (lpcrm_returned continuation_module) returned indices"
    using checked by (auto simp: lpc_check_return_split_def)
  have prefix: "precise_return_contract P (lpc_return_eval eta [(LPCGoals pre,interface)]) (lp_ild Q) ?t ?pre_ret"
    by (rule precise_return_module_link_contract[OF _ program _ known sn])
      (use checked in \<open>auto simp: lpc_check_return_split_def lpc_check_return_module_data_def\<close>)
  have continuation: "precise_return_contract P
      [(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t rho)) ?gs),rho)]
      (lp_ild Q) (?pre_ret rho) ?cont_ret"
    if domains: "\<And>x. D (rho x)" and reached: "(?t,?pre_ret rho)\<in>(lp_ild Q)\<^sup>*" for rho
  proof -
    have child_sn: "SN_on (lp_ild Q) {?pre_ret rho}"
      by (rule SN_on_subset2[OF _ SN_on_Image_rtrancl[OF sn]]) (use reached in auto)
    show ?thesis
      by (rule precise_return_continuation_contract[where nd="lpc_return_bridge_node (lpcrm_returned prefix_module) vs",
          OF _ program distinct indexed _ _ _ domains child_sn])
        (use checked in \<open>auto simp: lpc_return_bridge_node_def lpc_check_return_split_def lpc_check_return_module_data_def\<close>)
  qed
  have bridge: "(?cont_ret rho,[(returned,map (lpc_project_interface indices rho) [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
    for rho :: "nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
    using lpc_return_projection_edge_sound[OF projection, of rho] arity by auto
  show ?thesis
    by (rule precise_return_split_shape_contract[OF shape program prefix knowledge_domain[OF known] continuation bridge])
qed


end
end
