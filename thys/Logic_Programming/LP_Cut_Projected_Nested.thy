theory LP_Cut_Projected_Nested
  imports LP_Cut_Projected_Ground_Split
begin

datatype 'f lpc_projected_nested_action =
    LPCPTLocal "'f lpc_projected_action"
  | LPCPTSplit "(string \<times> nat) list" "nat list"
      "'f lpc_term lp_cut_goal list" "'f lpc_term lp_cut_goal list" "'f lpc_term list"
      nat "'f lpc_link" "string list" nat "'f lpc_link"
  | LPCPTGroundSplit "(string \<times> nat) list" "nat list"
      "'f lpc_term lp_cut_goal list" "'f lpc_term lp_cut_goal list" "'f lpc_term list"
      nat "'f lpc_link" "string list" nat "'f lpc_link" "nat list"
      "('f lp_cut_symbol,string) lp_clause list" "'f list" "'f lp_cut_symbol lp_ground_mode list"


fun lpc_check_projected_nested_action where
  "lpc_check_projected_nested_action child fuel P filtering R Q modules nds states nd ss returned arity (LPCPTLocal a) =
    lpc_check_projected_action fuel filtering R P nds states nd ss returned arity a"
| "lpc_check_projected_nested_action child fuel P filtering R Q modules nds states nd ss returned arity
    (LPCPTSplit bindings indices pre rest interface prefix_idx pe vs continuation_idx ce) =
    (prefix_idx<length modules \<and> continuation_idx<length modules \<and> child prefix_idx \<and> child continuation_idx \<and>
     lpc_check_projected_split fuel P filtering R Q nd ss returned arity bindings indices pre rest interface
       (modules!prefix_idx) pe vs (modules!continuation_idx) ce)"


| "lpc_check_projected_nested_action child fuel P filtering R Q modules nds states nd ss returned arity
    (LPCPTGroundSplit bindings indices pre rest interface prefix_idx pe vs continuation_idx ce positions groundQ Fs modes) =
    (prefix_idx<length modules \<and> continuation_idx<length modules \<and> child prefix_idx \<and> child continuation_idx \<and>
     lpc_check_projected_ground_split fuel P filtering R Q nd ss returned arity bindings indices pre rest interface
       (modules!prefix_idx) pe vs (modules!continuation_idx) ce positions groundQ Fs modes)"

fun lpc_check_projected_nested where
  "lpc_check_projected_nested fuel 0 P filtering R Q modules actions i = False"
| "lpc_check_projected_nested fuel (Suc k) P filtering R Q modules actions i =
    (i<length modules \<and> i<length actions \<and>
     (let m=modules!i; nds=lpcrm_nodes m; states=lpcrm_states m; acts=actions!i in
       lpcrm_actions m=[] \<and> length nds=length states \<and> length nds=length acts \<and>
       list_all (\<lambda>j. map fst (states!j)=lpcn_state (nds!j) \<and>
         lpc_check_projected_nested_action
           (lpc_check_projected_nested fuel k P filtering R Q modules actions) fuel P filtering R Q modules
           nds states (nds!j) (states!j) (lpcrm_returned m) (lpcrm_arity m) (acts!j)) [0..<length nds]))"

theorem lpc_check_projected_nested_sound:
  assumes checked: "lpc_check_projected_nested fuel k P filtering R Q modules actions i"
    and program: "lp_cut_source_program P"
  shows "lpc_projected_semantic_data P filtering R (lpcrm_nodes (modules!i)) (lpcrm_states (modules!i))
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
  have local: "lpc_return_contract P (lpc_return_eval nu (?states!j)) (lpc_projected_rel filtering (set R))
      [(lpcn_pred (?nds!j),map nu (lpcn_vars (?nds!j)))]
      (\<lambda>rho. [(?ret,map rho [0..<?arity])])"
    if bound: "j<length ?nds"
      and known: "lp_cut_knowledge (set (lpcn_ground (?nds!j))) (lpcn_guards (?nds!j)) nu"
      and initial: "lpc_observed filtering [(lpcn_pred (?nds!j),map nu (lpcn_vars (?nds!j)))]"
      and sn: "SN_on (lpc_projected_rel filtering (set R)) {[(lpcn_pred (?nds!j),map nu (lpcn_vars (?nds!j)))]}"
      and lower: "\<And>vs v. ([(lpcn_pred (?nds!j),map nu (lpcn_vars (?nds!j)))],v)\<in>(lpc_projected_rel filtering (set R))\<^sup>+ \<Longrightarrow>
        lpc_return_module_rep ?nds ?states vs v \<Longrightarrow>
        lpc_return_contract P vs (lpc_projected_rel filtering (set R)) v (\<lambda>rho. [(?ret,map rho [0..<?arity])])"
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
        by (rule lpc_checked_projected_action_contract[OF _ initial known lower])
          (use action LPCPTLocal in simp)
    next
      case (LPCPTSplit bindings indices pre rest interface prefix_idx pe vs continuation_idx ce)
      have pc: "lpc_check_projected_nested fuel k P filtering R Q modules actions prefix_idx"
        and cc: "lpc_check_projected_nested fuel k P filtering R Q modules actions continuation_idx"
        and boundary: "lpc_check_projected_split fuel P filtering R Q (?nds!j) (?states!j) ?ret ?arity
          bindings indices pre rest interface (modules!prefix_idx) pe vs (modules!continuation_idx) ce"
        using action LPCPTSplit by auto
      show ?thesis by (rule lpc_projected_split_contract[OF boundary
        Suc.hyps[OF pc] Suc.hyps[OF cc] program known initial sn])
    next
      case (LPCPTGroundSplit bindings indices pre rest interface prefix_idx pe vs continuation_idx ce positions groundQ Fs modes)
      have pc: "lpc_check_projected_nested fuel k P filtering R Q modules actions prefix_idx"
        and cc: "lpc_check_projected_nested fuel k P filtering R Q modules actions continuation_idx"
        and boundary: "lpc_check_projected_ground_split fuel P filtering R Q (?nds!j) (?states!j) ?ret ?arity
          bindings indices pre rest interface (modules!prefix_idx) pe vs (modules!continuation_idx) ce positions groundQ Fs modes"
        using action LPCPTGroundSplit by auto
      show ?thesis by (rule lpc_projected_ground_split_contract[OF boundary
        Suc.hyps[OF pc] Suc.hyps[OF cc] program known initial sn])

    qed
  qed
  show ?case unfolding lpc_projected_semantic_data_def
    by (intro allI impI, rule lpc_projected_table_semantic_contract[OF local lengths program])
qed

end
