theory LP_Cut_Domain_Return_Nested
 imports LP_Cut_Domain_Return_Semantic_Ground_Split
begin

context cut_runtime_domain
begin

theorem precise_check_return_nested_sound:
  assumes checked: "lpc_check_return_nested fuel k P Q modules actions i"
    and program: "lp_cut_source_program P"
  shows "precise_return_semantic_data P Q (lpcrm_nodes (modules!i)) (lpcrm_states (modules!i))
    (lpcrm_returned (modules!i)) (lpcrm_arity (modules!i))"
  using checked
proof (induct k arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc k)
  let ?m = "modules!i"
  let ?nds = "lpcrm_nodes ?m"
  let ?states = "lpcrm_states ?m"
  let ?ret = "lpcrm_returned ?m"
  let ?arity = "lpcrm_arity ?m"
  have lengths: "length ?nds=length ?states"
    using Suc.prems by (simp add: Let_def)
  have local: "precise_return_contract P (lpc_return_eval nu (?states!j)) (lp_ild Q)
      [(lpcn_pred (?nds!j),map nu (lpcn_vars (?nds!j)))]
      (\<lambda>rho. [(?ret,map rho [0..<?arity])])"
    if bound: "j<length ?nds"
      and known: "knowledge (set (lpcn_ground (?nds!j))) (lpcn_guards (?nds!j)) nu"
      and sn: "SN_on (lp_ild Q) {[(lpcn_pred (?nds!j),map nu (lpcn_vars (?nds!j)))]}"
      and lower: "\<And>vs v. ([(lpcn_pred (?nds!j),map nu (lpcn_vars (?nds!j)))],v)\<in>(lp_ild Q)\<^sup>+ \<Longrightarrow>
        precise_return_module_rep ?nds ?states vs v \<Longrightarrow>
        precise_return_contract P vs (lp_ild Q) v (\<lambda>rho. [(?ret,map rho [0..<?arity])])"
    for j nu
  proof -
    have action: "lpc_check_return_nested_action
      (lpc_check_return_nested fuel k P Q modules actions) fuel P Q modules
      ?nds ?states (?nds!j) (?states!j) ?ret ?arity (actions!i!j)"
      using Suc.prems bound by (auto simp: Let_def list_all_iff)
    show ?thesis
    proof (cases "actions!i!j")
      case (LPCTLocal a)
      show ?thesis
        by (rule precise_return_module_action_sound[OF _ known lower])
          (use action LPCTLocal in simp)
    next
      case (LPCTSplit bindings indices pre rest interface prefix_idx pe vs continuation_idx ce)
      have pc: "lpc_check_return_nested fuel k P Q modules actions prefix_idx"
        and cc: "lpc_check_return_nested fuel k P Q modules actions continuation_idx"
        and boundary: "lpc_check_return_semantic_split fuel P Q (?nds!j) (?states!j) ?ret ?arity
          bindings indices pre rest interface (modules!prefix_idx) pe vs (modules!continuation_idx) ce"
        using action LPCTSplit by auto
      show ?thesis by (rule precise_return_semantic_split_contract[OF boundary
        Suc.hyps[OF pc] Suc.hyps[OF cc] program known sn])
    next
      case (LPCTGroundSplit bindings indices pre rest interface prefix_idx pe vs continuation_idx ce positions groundQ Fs modes)
      have pc: "lpc_check_return_nested fuel k P Q modules actions prefix_idx"
        and cc: "lpc_check_return_nested fuel k P Q modules actions continuation_idx"
        and boundary: "lpc_check_semantic_ground_return_split fuel P Q (?nds!j) (?states!j) ?ret ?arity
          bindings indices pre rest interface (modules!prefix_idx) pe vs (modules!continuation_idx) ce positions groundQ Fs modes"
        using action LPCTGroundSplit by auto
      show ?thesis by (rule precise_semantic_ground_return_split_contract[OF boundary
        Suc.hyps[OF pc] Suc.hyps[OF cc] program known sn])
    qed
  qed
  show ?case unfolding precise_return_semantic_data_def
    by (intro allI impI, rule precise_return_table_semantic_contract[OF local lengths program])
qed


end
end
