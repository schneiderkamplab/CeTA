theory LP_Cut_Domain_Return_Semantic_Ground_Split
 imports LP_Cut_Domain_Return_Semantic_Split
begin

context cut_runtime_domain
begin

theorem precise_return_semantic_ground_continuation_contract:
  assumes module: "precise_return_semantic_data P Q nds states returned (length vs)"
    and program: "lp_cut_source_program P"
    and distinct: "distinct vs"
    and indexed: "lpc_return_indexed_goals (length vs) gs"
    and node: "lpcn_pred nd=entry_symbol" "lpcn_vars nd=vs"
    and link: "lpc_check_return_table_link fuel Q nds states nd
      [(LPCGoals (lpc_return_named_goals vs gs),map Var vs)] (map ((!) vs) positions) [] [] e"
    and grounds: "\<forall>i\<in>set positions. i<length vs \<and> lp_seg_ground (rho i)"
    and domains: "\<And>x. D (rho x)"
    and sn: "SN_on (lp_ild Q) {[(entry_symbol,map rho [0..<length vs])]}"
  shows "precise_return_contract P
    [(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t rho)) gs),rho)] (lp_ild Q)
    [(entry_symbol,map rho [0..<length vs])] (\<lambda>eta. [(returned,map eta [0..<length vs])])"
proof -
  let ?nu = "lp_cut_query_env vs (map rho [0..<length vs])"
  let ?ss = "[(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t rho)) gs),rho)]"
  let ?F = "lpc_project_interface [0..<length vs]"
  have tuple_values: "map ?nu vs=map rho [0..<length vs]"
    by (rule lp_cut_query_env_values) (use distinct in auto)
  have envD: "\<And>x. D (?nu x)" by (rule query_env_domain) (use domains in auto)
  have known: "knowledge (set (map ((!) vs) positions)) [] ?nu"
    using grounds envD by (auto simp: knowledge_def lpc_return_tuple_valuation[OF distinct])
  have child_sn: "SN_on (lp_ild Q) {[(lpcn_pred nd,map ?nu (lpcn_vars nd))]}"
    using sn node tuple_values by simp
  have contract: "precise_return_contract P
      (lpc_return_eval ?nu [(LPCGoals (lpc_return_named_goals vs gs),map Var vs)]) (lp_ild Q)
      [(lpcn_pred nd,map ?nu (lpcn_vars nd))] (\<lambda>eta. [(returned,map eta [0..<length vs])])"
    by (rule precise_return_semantic_link_contract[OF module program link known child_sn])
  have shape: "lpc_return_eval ?nu [(LPCGoals (lpc_return_named_goals vs gs),map Var vs)] =
      lpc_reinterface ?F ?ss"
    by (simp add: lpc_return_eval_def lpc_reinterface_def lpc_return_tuple_env[OF distinct]
      lpc_return_named_goals_eval[OF distinct indexed])
  have projected: "precise_return_contract P (lpc_reinterface ?F ?ss) (lp_ild Q)
      [(entry_symbol,map rho [0..<length vs])] (\<lambda>eta. [(returned,map eta [0..<length vs])])"
    using contract shape node tuple_values by simp
  have vector: "map (?F eta) [0..<length vs]=map eta [0..<length vs]" for eta
    by (rule map_cong) (auto simp: lpc_project_interface_def)
  show ?thesis
    by (rule precise_return_contract_lift_interface[where F="?F", OF lpc_project_interface_commutes projected])
      (simp add: vector)
qed


theorem precise_semantic_ground_return_split_contract:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_check_semantic_ground_return_split fuel P Q nd original returned arity
      bindings indices pre rest interface prefix_module prefix_link vs continuation_module continuation_link positions groundQ Fs modes"
    and prefix_module: "precise_return_semantic_data P Q (lpcrm_nodes prefix_module) (lpcrm_states prefix_module)
      (lpcrm_returned prefix_module) (lpcrm_arity prefix_module)"
    and continuation_module: "precise_return_semantic_data P Q (lpcrm_nodes continuation_module) (lpcrm_states continuation_module)
      (lpcrm_returned continuation_module) (lpcrm_arity continuation_module)"
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
    using checked by (auto simp: lpc_check_semantic_ground_return_split_def)
  have prefix: "precise_return_contract P (lpc_return_eval eta [(LPCGoals pre,interface)]) (lp_ild Q) ?t ?pre_ret"
    by (rule precise_return_semantic_link_contract[OF _ program _ known sn])
      (use checked prefix_module continuation_module in \<open>auto simp: lpc_check_semantic_ground_return_split_def precise_return_semantic_data_def\<close>)
  have continuation: "precise_return_contract P
      [(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t rho)) ?gs),rho)]
      (lp_ild Q) (?pre_ret rho) ?cont_ret"
    if actual: "precise_actual_return P (lpc_return_eval eta [(LPCGoals pre,interface)]) rho" for rho
  proof -
    have domains: "\<And>x. D (rho x)"
      by (rule precise_actual_return_domain[OF precise_environments_eval[OF knowledge_domain[OF known]] actual])
    have reached: "(?t,?pre_ret rho)\<in>(lp_ild Q)\<^sup>*"
      by (rule precise_actual_return_residual[OF prefix actual])
    have output_check: "lpc_check_return_output_groundness P pre (lpcn_ground nd) interface positions groundQ Fs modes"
      using checked by (simp add: lpc_check_semantic_ground_return_split_def)
    have inputs: "\<forall>x\<in>set (lpcn_ground nd). lp_seg_ground (eta x)"
      using known by (simp add: knowledge_def)
    have outputs: "\<forall>i\<in>set positions. lp_seg_ground (rho i)"
      by (rule precise_return_output_groundness_sound[OF output_check inputs actual])
    have grounds: "\<forall>i\<in>set positions. i<length vs \<and> lp_seg_ground (rho i)"
      using outputs checked by (auto simp: lpc_check_semantic_ground_return_split_def list_all_iff)
    have child_sn: "SN_on (lp_ild Q) {?pre_ret rho}"
      by (rule SN_on_subset2[OF _ SN_on_Image_rtrancl[OF sn]]) (use reached in auto)
    show ?thesis
      by (rule precise_return_semantic_ground_continuation_contract[where nd="lpc_return_bridge_node (lpcrm_returned prefix_module) vs",
          OF _ program distinct indexed _ _ _ grounds domains child_sn])
        (use checked prefix_module continuation_module in \<open>auto simp: lpc_return_bridge_node_def lpc_check_semantic_ground_return_split_def precise_return_semantic_data_def\<close>)
  qed
  have bridge: "(?cont_ret rho,[(returned,map (lpc_project_interface indices rho) [0..<arity])])\<in>(lp_ild Q)\<^sup>*"
    for rho :: "nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
    using lpc_return_projection_edge_sound[OF projection, of rho] arity by auto
  show ?thesis
    by (rule precise_return_split_shape_contract_actual[OF shape program prefix continuation bridge])
qed



end
end
