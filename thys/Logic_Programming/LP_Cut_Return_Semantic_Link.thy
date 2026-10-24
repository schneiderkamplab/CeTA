theory LP_Cut_Return_Semantic_Link
  imports LP_Cut_Return_Semantic_Module
begin

definition lpc_return_semantic_data where
  "lpc_return_semantic_data P Q nds states returned arity =
    (\<forall>i eta. i<length nds \<longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<longrightarrow>
      SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]} \<longrightarrow>
      lpc_return_contract P (lpc_return_eval eta (states!i)) (lp_ild Q)
        [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] (\<lambda>rho. [(returned,map rho [0..<arity])]))"

lemma lpc_return_semantic_dataD:
  assumes "lpc_return_semantic_data P Q nds states returned arity"
    "i<length nds"
    "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    "SN_on (lp_ild Q) {[(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))]}"
  shows "lpc_return_contract P (lpc_return_eval eta (states!i)) (lp_ild Q)
    [(lpcn_pred (nds!i),map eta (lpcn_vars (nds!i)))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
  using assms unfolding lpc_return_semantic_data_def by blast

theorem lpc_return_semantic_link_contract:
  assumes module: "lpc_return_semantic_data P Q nds states returned arity"
    and program: "lp_cut_source_program P"
    and link: "lpc_check_return_table_link fuel Q nds states nd ss G guards [] e"
    and known: "lp_cut_knowledge (set G) guards eta"
    and sn: "SN_on (lp_ild Q) {[(lpcn_pred nd,map eta (lpcn_vars nd))]}"
  shows "lpc_return_contract P (lpc_return_eval eta ss) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof -
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  obtain u swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
    and represented: "lpc_return_rep nds states (lpc_return_scope_word swaps (lpc_return_eval eta ss)) u"
    using lpc_return_table_link_sound[OF link equations refl known] by blast
  obtain j nu where bound: "j<length nds"
    and shape: "lpc_return_scope_word swaps (lpc_return_eval eta ss)=lpc_return_eval nu (states!j)"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (nds!j))) (lpcn_guards (nds!j)) nu"
    and u: "u=[(lpcn_pred (nds!j),map nu (lpcn_vars (nds!j)))]"
    using represented by (auto simp: lpc_return_rep_def)
  have child_sn: "SN_on (lp_ild Q) {u}"
    by (rule SN_on_subset2[OF _ SN_on_Image_rtrancl[OF sn]])
      (use trancl_into_rtrancl[OF strict] in auto)
  have child: "lpc_return_contract P (lpc_return_eval nu (states!j)) (lp_ild Q) u
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    unfolding u by (rule lpc_return_semantic_dataD[OF module bound knowledge])
      (use child_sn u in simp)
  have restored: "lpc_return_contract P
    (lpc_return_scope_word (rev swaps) (lpc_return_eval nu (states!j))) (lp_ild Q) u
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule lpc_return_contract_scopes[OF program child])
  have original: "lpc_return_contract P (lpc_return_eval eta ss) (lp_ild Q) u
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    using restored by (simp add: shape[symmetric] lpc_return_scope_word_inverse)
  show ?thesis by (rule lpc_return_contract_start[OF trancl_into_rtrancl[OF strict] original])
qed

theorem lpc_return_semantic_continuation_contract:
  assumes module: "lpc_return_semantic_data P Q nds states returned (length vs)"
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
    by (rule lpc_return_semantic_link_contract[OF module program link known child_sn])
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

