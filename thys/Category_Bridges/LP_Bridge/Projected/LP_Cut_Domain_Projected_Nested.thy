theory LP_Cut_Domain_Projected_Nested
 imports LP_Cut_Domain_Projected_Ground_Split
begin

hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_check_projected_nested_sound:
  assumes checked: "lpc_check_projected_nested fuel k P filtering R Q modules actions i"
    and program: "lp_cut_source_program P"
  shows "precise_projected_semantic_data P filtering R (lpcrm_nodes (modules!i)) (lpcrm_states (modules!i))
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
  have local: "precise_return_contract P (lpc_return_eval nu (?states!j)) (lpc_projected_rel filtering (set R))
      [(lpcn_pred (?nds!j),map nu (lpcn_vars (?nds!j)))]
      (\<lambda>rho. [(?ret,map rho [0..<?arity])])"
    if bound: "j<length ?nds"
      and known: "knowledge (set (lpcn_ground (?nds!j))) (lpcn_guards (?nds!j)) nu"
      and initial: "lpc_observed filtering [(lpcn_pred (?nds!j),map nu (lpcn_vars (?nds!j)))]"
      and sn: "SN_on (lpc_projected_rel filtering (set R)) {[(lpcn_pred (?nds!j),map nu (lpcn_vars (?nds!j)))]}"
      and lower: "\<And>vs v. ([(lpcn_pred (?nds!j),map nu (lpcn_vars (?nds!j)))],v)\<in>(lpc_projected_rel filtering (set R))\<^sup>+ \<Longrightarrow>
        precise_return_module_rep ?nds ?states vs v \<Longrightarrow>
        precise_return_contract P vs (lpc_projected_rel filtering (set R)) v (\<lambda>rho. [(?ret,map rho [0..<?arity])])"
    for j nu
  proof -
    have action: "lpc_check_projected_nested_action
      (lpc_check_projected_nested fuel k P filtering R Q modules actions) fuel P filtering R Q modules
      ?nds ?states (?nds!j) (?states!j) ?ret ?arity (actions!i!j)"
      using Suc.prems bound by (auto simp: Let_def list_all_iff)
    show ?thesis
    proof (cases "actions!i!j")
      case (LPCPTLocal a)
      show ?thesis
        by (rule precise_checked_projected_action_contract[OF _ initial known lower])
          (use action LPCPTLocal in simp)
    next
      case (LPCPTSplit bindings indices pre rest interface prefix_idx pe vs continuation_idx ce)
      have pc: "lpc_check_projected_nested fuel k P filtering R Q modules actions prefix_idx"
        and cc: "lpc_check_projected_nested fuel k P filtering R Q modules actions continuation_idx"
        and boundary: "lpc_check_projected_split fuel P filtering R Q (?nds!j) (?states!j) ?ret ?arity
          bindings indices pre rest interface (modules!prefix_idx) pe vs (modules!continuation_idx) ce"
        using action LPCPTSplit by auto
      show ?thesis by (rule precise_projected_split_contract[OF boundary
        Suc.hyps[OF pc] Suc.hyps[OF cc] program known initial sn])
    next
      case (LPCPTGroundSplit bindings indices pre rest interface prefix_idx pe vs continuation_idx ce positions groundQ Fs modes)
      have pc: "lpc_check_projected_nested fuel k P filtering R Q modules actions prefix_idx"
        and cc: "lpc_check_projected_nested fuel k P filtering R Q modules actions continuation_idx"
        and boundary: "lpc_check_projected_ground_split fuel P filtering R Q (?nds!j) (?states!j) ?ret ?arity
          bindings indices pre rest interface (modules!prefix_idx) pe vs (modules!continuation_idx) ce positions groundQ Fs modes"
        using action LPCPTGroundSplit by auto
      show ?thesis by (rule precise_projected_ground_split_contract[OF boundary
        Suc.hyps[OF pc] Suc.hyps[OF cc] program known initial sn])

    qed
  qed
  show ?case unfolding precise_projected_semantic_data_def
    by (intro allI impI, rule precise_projected_table_semantic_contract[OF local lengths program])
qed


end
end
