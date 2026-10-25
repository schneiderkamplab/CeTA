theory LP_Cut_Projected_Ground_Split
 imports LP_Cut_Projected_Split LP_Cut_Return_Semantic_Ground_Split
begin

theorem lpc_projected_ground_continuation_contract:
  assumes module: "lpc_projected_semantic_data P filtering R nds states returned (length vs)"
    and program: "lp_cut_source_program P"
    and distinct: "distinct vs"
    and indexed: "lpc_return_indexed_goals (length vs) gs"
    and node: "lpcn_pred nd=entry_symbol" "lpcn_vars nd=vs"
    and link: "lpc_check_return_table_link fuel Q nds states nd
      [(LPCGoals (lpc_return_named_goals vs gs),map Var vs)] (map ((!) vs) positions) [] [] e"
    and rule: "lpc_check_projected_link_rule filtering R nd nds e"
    and initial: "lpc_observed filtering [(entry_symbol,map rho [0..<length vs])]"
    and grounds: "\<forall>i\<in>set positions. i<length vs \<and> lp_seg_ground (rho i)"
    and sn: "SN_on (lpc_projected_rel filtering (set R)) {[(entry_symbol,map rho [0..<length vs])]}"
  shows "lpc_return_contract P
    [(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t rho)) gs),rho)] (lpc_projected_rel filtering (set R))
    [(entry_symbol,map rho [0..<length vs])] (\<lambda>eta. [(returned,map eta [0..<length vs])])"
proof -
  let ?nu = "lp_cut_query_env vs (map rho [0..<length vs])"
  let ?ss = "[(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t rho)) gs),rho)]"
  let ?F = "lpc_project_interface [0..<length vs]"
  have tuple_values: "map ?nu vs=map rho [0..<length vs]"
    by (rule lp_cut_query_env_values) (use distinct in auto)
  have known: "lp_cut_knowledge (set (map ((!) vs) positions)) [] ?nu"
    using grounds by (auto simp: lp_cut_knowledge_def lpc_return_tuple_valuation[OF distinct])
  have child_sn: "SN_on (lpc_projected_rel filtering (set R)) {[(lpcn_pred nd,map ?nu (lpcn_vars nd))]}"
    using sn node tuple_values by simp
  have child_good: "lpc_observed filtering [(lpcn_pred nd,map ?nu (lpcn_vars nd))]"
    using initial node tuple_values by simp
  have contract: "lpc_return_contract P
      (lpc_return_eval ?nu [(LPCGoals (lpc_return_named_goals vs gs),map Var vs)]) (lpc_projected_rel filtering (set R))
      [(lpcn_pred nd,map ?nu (lpcn_vars nd))] (\<lambda>eta. [(returned,map eta [0..<length vs])])"
    by (rule lpc_projected_semantic_link_contract[OF module program link known rule child_good child_sn])
  have shape: "lpc_return_eval ?nu [(LPCGoals (lpc_return_named_goals vs gs),map Var vs)] =
      lpc_reinterface ?F ?ss"
    by (simp add: lpc_return_eval_def lpc_reinterface_def lpc_return_tuple_env[OF distinct]
      lpc_return_named_goals_eval[OF distinct indexed])
  have projected: "lpc_return_contract P (lpc_reinterface ?F ?ss) (lpc_projected_rel filtering (set R))
      [(entry_symbol,map rho [0..<length vs])] (\<lambda>eta. [(returned,map eta [0..<length vs])])"
    using contract shape node tuple_values by simp
  have vector: "map (?F eta) [0..<length vs]=map eta [0..<length vs]" for eta
    by (rule map_cong) (auto simp: lpc_project_interface_def)
  show ?thesis
    by (rule lpc_return_contract_lift_interface[where F="?F", OF lpc_project_interface_commutes projected])
      (simp add: vector)
qed

theorem lpc_projected_split_shape_actual_contract:
  assumes checked: "lpc_check_return_split_shape bindings indices pre rest interface original"
    and program: "lp_cut_source_program P"
    and prefix: "lpc_return_contract P (lpc_return_eval eta [(LPCGoals pre,interface)]) R t ret"
    and continuation: "\<And>rho. lpc_actual_return P (lpc_return_eval eta [(LPCGoals pre,interface)]) rho \<Longrightarrow>
      lpc_return_contract P
        [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho))
          (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)),rho)] R (ret rho) extended"
    and bridge: "\<And>rho. (t,extended rho)\<in>R\<^sup>* \<Longrightarrow> (extended rho,final (lpc_project_interface indices rho))\<in>R\<^sup>*"
  shows "lpc_return_contract P (lpc_return_eval eta original) R t final"
proof -
  have composed: "lpc_return_contract P
    (lpc_attach_answers (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)
      (lpc_return_eval eta [(LPCGoals pre,interface)])) R t extended"
    by (rule lpc_return_contract_compose_actual[OF program prefix])
      (use continuation in \<open>auto simp: lpc_return_eval_def\<close>)
  have projected: "lpc_return_contract P
    (lpc_reinterface (lpc_project_interface indices)
      (lpc_attach_answers (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)
        (lpc_return_eval eta [(LPCGoals pre,interface)]))) R t final"
    by (rule lpc_return_contract_project_reachable[OF lpc_project_interface_commutes composed bridge])
  show ?thesis using projected lpc_return_split_shape_sound[OF checked, of eta] by simp
qed


definition lpc_check_projected_ground_split where
  "lpc_check_projected_ground_split fuel P filtering R Q nd original returned arity
      bindings indices pre rest interface prefix_module prefix_link vs continuation_module continuation_link positions groundQ Fs modes =
    (lpc_check_return_split_shape bindings indices pre rest interface original \<and>
     lpc_check_return_output_groundness P pre (lpcn_ground nd) interface positions groundQ Fs modes \<and>
     list_all (\<lambda>i. i<length vs) positions \<and>
     length indices=arity \<and> length vs=length interface \<and> distinct vs \<and>
     lpcrm_arity prefix_module=length vs \<and> lpcrm_arity continuation_module=length vs \<and>
     lpc_return_indexed_goals (length vs) (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest) \<and>
     lpc_check_return_table_link fuel Q (lpcrm_nodes prefix_module) (lpcrm_states prefix_module)
       nd [(LPCGoals pre,interface)] (lpcn_ground nd) (lpcn_guards nd) [] prefix_link \<and>
     lpc_check_return_table_link fuel Q (lpcrm_nodes continuation_module) (lpcrm_states continuation_module)
       (lpc_return_bridge_node (lpcrm_returned prefix_module) vs)
       [(LPCGoals (lpc_return_named_goals vs (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)),map Var vs)]
       (map ((!) vs) positions) [] [] continuation_link \<and>
     lpc_check_return_projection_edge Q vs (lpcrm_returned continuation_module) returned indices \<and>
     lpc_check_projected_link_rule filtering R nd (lpcrm_nodes prefix_module) prefix_link \<and>
     lpc_check_projected_link_rule filtering R
       (lpc_return_bridge_node (lpcrm_returned prefix_module) vs)
       (lpcrm_nodes continuation_module) continuation_link \<and>
     lpc_check_projected_clauses filtering R
       [((lpcrm_returned continuation_module,map Var vs),[(returned,map (\<lambda>i. Var (vs!i)) indices)])])"

theorem lpc_projected_ground_split_contract:
  fixes P :: "('f,string) lp_cut_program"
  assumes checked: "lpc_check_projected_ground_split fuel P filtering R Q nd original returned arity
      bindings indices pre rest interface prefix_module prefix_link vs continuation_module continuation_link positions groundQ Fs modes"
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
    using checked by (auto simp: lpc_check_projected_ground_split_def)
  have prefix: "lpc_return_contract P (lpc_return_eval eta [(LPCGoals pre,interface)]) (lpc_projected_rel filtering (set R)) ?t ?pre_ret"
    by (rule lpc_projected_semantic_link_contract[OF _ program _ known _ initial sn])
      (use checked prefix_module continuation_module in \<open>auto simp: lpc_check_projected_ground_split_def lpc_projected_semantic_data_def\<close>)
  have continuation: "lpc_return_contract P
      [(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t rho)) ?gs),rho)]
      (lpc_projected_rel filtering (set R)) (?pre_ret rho) ?cont_ret"
    if actual: "lpc_actual_return P (lpc_return_eval eta [(LPCGoals pre,interface)]) rho" for rho
  proof -
    have reached: "(?t,?pre_ret rho)\<in>(lpc_projected_rel filtering (set R))\<^sup>*"
      by (rule lpc_actual_return_residual[OF prefix actual])
    have output_check: "lpc_check_return_output_groundness P pre (lpcn_ground nd) interface positions groundQ Fs modes"
      using checked by (simp add: lpc_check_projected_ground_split_def)
    have inputs: "\<forall>x\<in>set (lpcn_ground nd). lp_seg_ground (eta x)"
      using known by (simp add: lp_cut_knowledge_def)
    have outputs: "\<forall>i\<in>set positions. lp_seg_ground (rho i)"
      by (rule lpc_return_output_groundness_sound[OF output_check inputs actual])
    have grounds: "\<forall>i\<in>set positions. i<length vs \<and> lp_seg_ground (rho i)"
      using outputs checked by (auto simp: lpc_check_projected_ground_split_def list_all_iff)
    have child_sn: "SN_on (lpc_projected_rel filtering (set R)) {?pre_ret rho}"
      by (rule SN_on_subset2[OF _ SN_on_Image_rtrancl[OF sn]]) (use reached in auto)
    have child_good: "lpc_observed filtering (?pre_ret rho)"
      by (rule lpc_projected_reachable_observed[OF reached initial])
    show ?thesis
      by (rule lpc_projected_ground_continuation_contract[where nd="lpc_return_bridge_node (lpcrm_returned prefix_module) vs",
          OF _ program distinct indexed _ _ _ _ child_good grounds child_sn])
        (use checked prefix_module continuation_module in \<open>auto simp: lpc_return_bridge_node_def lpc_check_projected_ground_split_def lpc_projected_semantic_data_def\<close>)
  qed
  let ?Qp = "[((lpcrm_returned continuation_module,map Var vs),[(returned,map (\<lambda>i. Var (vs!i)) indices)])]"
  have projection_local: "lpc_check_return_projection_edge ?Qp vs (lpcrm_returned continuation_module) returned indices"
    using projection by (auto simp: lpc_check_return_projection_edge_def)
  have rules: "lpc_check_projected_clauses filtering R ?Qp"
    using checked by (simp add: lpc_check_projected_ground_split_def)
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
    by (rule lpc_projected_split_shape_actual_contract[OF shape program prefix continuation bridge])
qed

end
