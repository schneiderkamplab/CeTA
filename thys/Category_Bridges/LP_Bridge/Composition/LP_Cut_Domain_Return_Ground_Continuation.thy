theory LP_Cut_Domain_Return_Ground_Continuation
 imports LP_Cut_Domain_Return_Output_Groundness
begin

context cut_runtime_domain
begin

theorem precise_return_ground_continuation_contract:
  assumes module: "lpc_check_return_module fuel P Q nds states returned (length vs) actions"
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
    by (rule precise_return_module_link_contract[OF module program link known child_sn])
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

theorem precise_return_split_shape_contract_actual:
  assumes checked: "lpc_check_return_split_shape bindings indices pre rest interface original"
    and program: "lp_cut_source_program P"
    and prefix: "precise_return_contract P (lpc_return_eval eta [(LPCGoals pre,interface)]) R t ret"
    and continuation: "\<And>rho. precise_actual_return P (lpc_return_eval eta [(LPCGoals pre,interface)]) rho \<Longrightarrow>
      precise_return_contract P
        [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho))
          (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)),rho)] R (ret rho) extended"
    and bridge: "\<And>rho. (extended rho,final (lpc_project_interface indices rho))\<in>R\<^sup>*"
  shows "precise_return_contract P (lpc_return_eval eta original) R t final"
proof -
  have composed: "precise_return_contract P
    (lpc_attach_answers (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)
      (lpc_return_eval eta [(LPCGoals pre,interface)])) R t extended"
    by (rule precise_return_contract_compose_actual[OF program prefix])
      (use continuation in \<open>auto simp: lpc_return_eval_def\<close>)
  have projected: "precise_return_contract P
    (lpc_reinterface (lpc_project_interface indices)
      (lpc_attach_answers (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)
        (lpc_return_eval eta [(LPCGoals pre,interface)]))) R t final"
    by (rule precise_return_contract_project[OF lpc_project_interface_commutes composed bridge])
  show ?thesis using projected lpc_return_split_shape_sound[OF checked, of eta] by simp
qed


end
end
