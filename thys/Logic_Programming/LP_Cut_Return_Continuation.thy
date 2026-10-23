theory LP_Cut_Return_Continuation
  imports LP_Cut_Return_Module_Link LP_Cut_Return_Interface_Lift
begin

definition lpc_return_indexed_goals where
  "lpc_return_indexed_goals n gs =
    (\<forall>g\<in>set gs. \<forall>t\<in>set (lp_cut_terms g). \<forall>i\<in>vars_term t. i<n)"

definition lpc_return_named_goals where
  "lpc_return_named_goals vs gs = map (lp_cut_map (map_term id ((!) vs))) gs"

lemma lpc_return_tuple_valuation:
  assumes distinct: "distinct vs" and bound: "i<length vs"
  shows "lp_cut_query_env vs (map rho [0..<length vs]) (vs!i)=rho i"
proof -
  have tuple_values: "map (lp_cut_query_env vs (map rho [0..<length vs])) vs=map rho [0..<length vs]"
    by (rule lp_cut_query_env_values) (use distinct in auto)
  show ?thesis using arg_cong[OF tuple_values, of "\<lambda>xs. xs!i"] bound by simp
qed

lemma lpc_return_named_term:
  assumes "distinct vs" "\<forall>i\<in>vars_term t. i<length vs"
  shows "lp_ieval (map_term id ((!) vs) t) (lp_cut_query_env vs (map rho [0..<length vs])) = lp_ieval t rho"
  using assms(2)
  by (induct t) (auto simp: lpc_return_tuple_valuation[OF assms(1)] intro!: map_cong)

lemma lpc_return_named_goals_eval:
  assumes "distinct vs" "lpc_return_indexed_goals (length vs) gs"
  shows "map (lp_cut_map (\<lambda>t. lp_ieval t (lp_cut_query_env vs (map rho [0..<length vs]))))
    (lpc_return_named_goals vs gs) = map (lp_cut_map (\<lambda>t. lp_ieval t rho)) gs"
proof -
  have local: "lp_cut_map (\<lambda>t. lp_ieval t (lp_cut_query_env vs (map rho [0..<length vs])))
      (lp_cut_map (map_term id ((!) vs)) g) = lp_cut_map (\<lambda>t. lp_ieval t rho) g"
    if "g\<in>set gs" for g
    using assms(2) that unfolding lpc_return_indexed_goals_def
    by (cases g) (auto intro!: lpc_return_named_term[OF assms(1)])
  show ?thesis using local by (simp add: lpc_return_named_goals_def map_map o_def cong: map_cong)
qed

lemma lpc_return_tuple_env:
  assumes "distinct vs"
  shows "lpc_return_env (map Var vs) (lp_cut_query_env vs (map rho [0..<length vs])) =
    lpc_project_interface [0..<length vs] rho"
  by (rule ext) (simp add: lpc_return_env_def lpc_project_interface_def lpc_return_tuple_valuation[OF assms])

theorem lpc_return_continuation_contract:
  assumes module: "lpc_check_return_module fuel P Q nds states returned (length vs) actions"
    and program: "lp_cut_source_program P"
    and distinct: "distinct vs"
    and indexed: "lpc_return_indexed_goals (length vs) gs"
    and node: "lpcn_pred nd=entry_symbol" "lpcn_vars nd=vs"
    and link: "lpc_check_return_table_link fuel Q nds states nd
      [(LPCGoals (lpc_return_named_goals vs gs),map Var vs)] [] [] [] e"
    and sn: "SN_on (lp_ild Q) {[(entry_symbol,map rho [0..<length vs])]}"
  shows "lpc_return_contract P
    [(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t rho)) gs),rho)] (lp_ild Q)
    [(entry_symbol,map rho [0..<length vs])] (\<lambda>eta. [(returned,map eta [0..<length vs])])"
proof -
  let ?nu = "lp_cut_query_env vs (map rho [0..<length vs])"
  let ?ss = "[(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t rho)) gs),rho)]"
  let ?F = "lpc_project_interface [0..<length vs]"
  have tuple_values: "map ?nu vs=map rho [0..<length vs]"
    by (rule lp_cut_query_env_values) (use distinct in auto)
  have known: "lp_cut_knowledge (set []) [] ?nu" by (simp add: lp_cut_knowledge_def)
  have child_sn: "SN_on (lp_ild Q) {[(lpcn_pred nd,map ?nu (lpcn_vars nd))]}"
    using sn node tuple_values by simp
  have contract: "lpc_return_contract P
      (lpc_return_eval ?nu [(LPCGoals (lpc_return_named_goals vs gs),map Var vs)]) (lp_ild Q)
      [(lpcn_pred nd,map ?nu (lpcn_vars nd))] (\<lambda>eta. [(returned,map eta [0..<length vs])])"
    by (rule lpc_return_module_link_contract[OF module program link known child_sn])
  have shape: "lpc_return_eval ?nu [(LPCGoals (lpc_return_named_goals vs gs),map Var vs)] =
      lpc_reinterface ?F ?ss"
    by (simp add: lpc_return_eval_def lpc_reinterface_def lpc_return_tuple_env[OF distinct]
      lpc_return_named_goals_eval[OF distinct indexed])
  have projected: "lpc_return_contract P (lpc_reinterface ?F ?ss) (lp_ild Q)
      [(entry_symbol,map rho [0..<length vs])] (\<lambda>eta. [(returned,map eta [0..<length vs])])"
    using contract shape node tuple_values by simp
  have vector: "map (?F eta) [0..<length vs]=map eta [0..<length vs]" for eta
    by (rule map_cong) (auto simp: lpc_project_interface_def)
  show ?thesis
    by (rule lpc_return_contract_lift_interface[where F="?F", OF lpc_project_interface_commutes projected])
      (simp add: vector)
qed

end
