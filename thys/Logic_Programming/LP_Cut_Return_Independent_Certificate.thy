theory LP_Cut_Return_Independent_Certificate
 imports LP_Cut_Return_Entry_Certificate LP_Cut_Return_Independent_Split
begin

definition lpc_return_ground_entry where
  "lpc_return_ground_entry f vs positions =
    (lpc_return_bridge_node f vs)\<lparr>lpcn_ground:=map ((!) vs) positions\<rparr>"

definition lpc_check_independent_split_certificate where
  "lpc_check_independent_split_certificate I J fuel P nd original
      bindings indices pre rest interface positions groundQ Fs modes
      pm pe pc vs entry_symbol cm ce cc =
    (lp_cut_source_program P \<and>
     lpc_check_return_split_shape bindings indices pre rest interface original \<and>
     lpc_check_return_output_groundness P pre (lpcn_ground nd) interface positions groundQ Fs modes \<and>
     length vs=length interface \<and> distinct vs \<and>
     list_all (\<lambda>i. i<length vs) positions \<and>
     lpc_return_indexed_goals (length vs) (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest) \<and>
     lpc_check_return_entry_certificate I J fuel P nd [(LPCGoals pre,interface)] pm pe pc \<and>
     lpc_check_return_entry_certificate I J fuel P (lpc_return_ground_entry entry_symbol vs positions)
       [(LPCGoals (lpc_return_named_goals vs (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)),map Var vs)] cm ce cc)"

theorem lpc_check_independent_split_certificate_sound:
  fixes P :: "('f,string) lp_cut_program"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and checked: "lpc_check_independent_split_certificate I J fuel P nd original
      bindings indices pre rest interface positions groundQ Fs modes pm pe pc vs entry_symbol cm ce cc"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
  shows "SN_on (lp_cut_mgu_source P) {map fst (lpc_return_eval eta original)}"
proof -
  let ?gs = "map (lp_cut_map (map_term id (lpc_return_route bindings))) rest"
  have shape: "lpc_check_return_split_shape bindings indices pre rest interface original"
    and program: "lp_cut_source_program P"
    and ground_check: "lpc_check_return_output_groundness P pre (lpcn_ground nd) interface positions groundQ Fs modes"
    and distinct: "distinct vs" and bounds: "list_all (\<lambda>i. i<length vs) positions"
    and indexed: "lpc_return_indexed_goals (length vs) ?gs"
    and prefix_check: "lpc_check_return_entry_certificate I J fuel P nd [(LPCGoals pre,interface)] pm pe pc"
    and tail_check: "lpc_check_return_entry_certificate I J fuel P (lpc_return_ground_entry entry_symbol vs positions)
       [(LPCGoals (lpc_return_named_goals vs ?gs),map Var vs)] cm ce cc"
    using checked by (auto simp: lpc_check_independent_split_certificate_def)
  have prefix: "lpc_return_contract P (lpc_return_eval eta [(LPCGoals pre,interface)])
      (lp_ild (lpcrc_source pc)) [(lpcn_pred nd,map eta (lpcn_vars nd))]
      (\<lambda>rho. [(lpcrm_returned pm,map rho [0..<lpcrm_arity pm])])"
    by (rule lpc_check_return_entry_certificate_sound[OF I J prefix_check known])
  have initial_ground: "\<forall>x\<in>set (lpcn_ground nd). lp_seg_ground (eta x)"
    using known by (simp add: lp_cut_knowledge_def)
  show ?thesis
  proof (rule lpc_return_ground_split_independent_SN[OF shape program prefix ground_check initial_ground])
    fix rho :: "nat \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
    assume grounds: "\<forall>i\<in>set positions. lp_seg_ground (rho i)"
    let ?nu = "lp_cut_query_env vs (map rho [0..<length vs])"
    let ?nd = "lpc_return_ground_entry entry_symbol vs positions"
    have knowledge: "lp_cut_knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?nu"
      using grounds bounds
      by (auto simp: lpc_return_ground_entry_def lpc_return_bridge_node_def lp_cut_knowledge_def
        list_all_iff lpc_return_tuple_valuation[OF distinct])
    have contract: "lpc_return_contract P
      (lpc_return_eval ?nu [(LPCGoals (lpc_return_named_goals vs ?gs),map Var vs)])
      (lp_ild (lpcrc_source cc)) [(lpcn_pred ?nd,map ?nu (lpcn_vars ?nd))]
      (\<lambda>tau. [(lpcrm_returned cm,map tau [0..<lpcrm_arity cm])])"
      by (rule lpc_check_return_entry_certificate_sound[OF I J tail_check knowledge])
    show "SN_on (lp_cut_mgu_source P) {[LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) ?gs)]}"
      using contract by (simp add: lpc_return_contract_def lpc_return_eval_def
        lpc_return_named_goals_eval[OF distinct indexed])
  qed
qed

end
