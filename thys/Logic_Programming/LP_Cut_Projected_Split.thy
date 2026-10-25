theory LP_Cut_Projected_Split
  imports LP_Cut_Projected_Split_Shape LP_Cut_Return_Semantic_Split
begin

definition lpc_check_projected_split where
  "lpc_check_projected_split fuel P filtering R Q nd original returned arity
      bindings indices pre rest interface prefix_module prefix_link vs continuation_module continuation_link =
    (lpc_check_return_split_shape bindings indices pre rest interface original \<and>
     length indices=arity \<and> length vs=length interface \<and> distinct vs \<and>
     lpcrm_arity prefix_module=length vs \<and> lpcrm_arity continuation_module=length vs \<and>
     lpc_return_indexed_goals (length vs) (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest) \<and>
     lpc_check_return_table_link fuel Q (lpcrm_nodes prefix_module) (lpcrm_states prefix_module)
       nd [(LPCGoals pre,interface)] (lpcn_ground nd) (lpcn_guards nd) [] prefix_link \<and>
     lpc_check_return_table_link fuel Q (lpcrm_nodes continuation_module) (lpcrm_states continuation_module)
       (lpc_return_bridge_node (lpcrm_returned prefix_module) vs)
       [(LPCGoals (lpc_return_named_goals vs (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)),map Var vs)]
       [] [] [] continuation_link \<and>
     lpc_check_return_projection_edge Q vs (lpcrm_returned continuation_module) returned indices \<and>
     lpc_check_projected_link_rule filtering R nd (lpcrm_nodes prefix_module) prefix_link \<and>
     lpc_check_projected_link_rule filtering R
       (lpc_return_bridge_node (lpcrm_returned prefix_module) vs)
       (lpcrm_nodes continuation_module) continuation_link \<and>
     lpc_check_projected_clauses filtering R
       [((lpcrm_returned continuation_module,map Var vs),[(returned,map (\<lambda>i. Var (vs!i)) indices)])])"

theorem lpc_projected_split_contract:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_check_projected_split fuel P filtering R Q nd original returned arity
      bindings indices pre rest interface prefix_module prefix_link vs continuation_module continuation_link"
    and prefix_module: "lpc_projected_semantic_data P filtering R (lpcrm_nodes prefix_module) (lpcrm_states prefix_module)
      (lpcrm_returned prefix_module) (lpcrm_arity prefix_module)"
    and continuation_module: "lpc_projected_semantic_data P filtering R (lpcrm_nodes continuation_module) (lpcrm_states continuation_module)
      (lpcrm_returned continuation_module) (lpcrm_arity continuation_module)"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and initial: "lpc_observed filtering [(lpcn_pred nd,map eta (lpcn_vars nd))]"
    and sn: "SN_on (lpc_projected_rel filtering (set R)) {[(lpcn_pred nd,map eta (lpcn_vars nd))]}"
  shows "lpc_return_contract P (lpc_return_eval eta original) (lpc_projected_rel filtering (set R))
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
    using checked by (auto simp: lpc_check_projected_split_def)
  have prefix: "lpc_return_contract P (lpc_return_eval eta [(LPCGoals pre,interface)]) (lpc_projected_rel filtering (set R)) ?t ?pre_ret"
    by (rule lpc_projected_semantic_link_contract[OF _ program _ known _ initial sn])
      (use checked prefix_module continuation_module in \<open>auto simp: lpc_check_projected_split_def lpc_projected_semantic_data_def\<close>)
  have continuation: "lpc_return_contract P
      [(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t rho)) ?gs),rho)]
      (lpc_projected_rel filtering (set R)) (?pre_ret rho) ?cont_ret"
    if reached: "(?t,?pre_ret rho)\<in>(lpc_projected_rel filtering (set R))\<^sup>*" for rho
  proof -
    have child_sn: "SN_on (lpc_projected_rel filtering (set R)) {?pre_ret rho}"
      by (rule SN_on_subset2[OF _ SN_on_Image_rtrancl[OF sn]]) (use reached in auto)
    have child_good: "lpc_observed filtering (?pre_ret rho)"
      by (rule lpc_projected_reachable_observed[OF reached initial])
    show ?thesis
      by (rule lpc_projected_semantic_continuation_contract[where nd="lpc_return_bridge_node (lpcrm_returned prefix_module) vs",
          OF _ program distinct indexed _ _ _ _ child_good child_sn])
        (use checked prefix_module continuation_module in \<open>auto simp: lpc_return_bridge_node_def lpc_check_projected_split_def lpc_projected_semantic_data_def\<close>)
  qed
  let ?Qp = "[((lpcrm_returned continuation_module,map Var vs),[(returned,map (\<lambda>i. Var (vs!i)) indices)])]"
  have projection_local: "lpc_check_return_projection_edge ?Qp vs (lpcrm_returned continuation_module) returned indices"
    using projection by (auto simp: lpc_check_return_projection_edge_def)
  have rules: "lpc_check_projected_clauses filtering R ?Qp"
    using checked by (simp add: lpc_check_projected_split_def)
  have bridge: "(?cont_ret rho,[(returned,map (lpc_project_interface indices rho) [0..<arity])])\<in>(lpc_projected_rel filtering (set R))\<^sup>*"
    if reached: "(?t,?cont_ret rho)\<in>(lpc_projected_rel filtering (set R))\<^sup>*"
    for rho :: "nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  proof -
    have good: "lpc_observed filtering (?cont_ret rho)"
      by (rule lpc_projected_reachable_observed[OF reached initial])
    obtain m where obs: "lpc_observes filtering (?cont_ret rho) m"
      using good unfolding lpc_observed_def by blast
    have edge: "(?cont_ret rho,[(returned,map (lpc_project_interface indices rho) [0..<length indices])])\<in>lp_ild ?Qp"
      by (rule lpc_return_projection_edge_sound[OF projection_local])
    have projected: "(?cont_ret rho,[(returned,map (lpc_project_interface indices rho) [0..<length indices])])\<in>lpc_projected_rel filtering (set R)"
      by (rule lpc_projected_clause_step[OF rules edge obs])
    show ?thesis using projected arity by auto
  qed
  show ?thesis
    by (rule lpc_return_split_shape_reachable_contract[OF shape program prefix continuation bridge])
qed

end
