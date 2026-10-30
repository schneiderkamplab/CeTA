theory LP_Prolog_Context_Module_Semantics
 imports LP_Prolog_Context_Split
begin

text \<open>Separate a module's checked source contract from its concrete action
encoding. Referenced modules may use a different checked proof constructor;
their termination child alone does not establish this contract.\<close>

definition lpp_context_data_semantics where
  "lpp_context_data_semantics (SP :: string lpp_success_clause list) P Q m = (\<forall>i (eta :: string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm).
    i < length (lppcm_nodes m) \<longrightarrow>
    lp_cut_knowledge (set (lpcn_ground (lppcm_nodes m!i))) (lpcn_guards (lppcm_nodes m!i)) eta \<longrightarrow>
    lpp_source_context_holds SP (lppcm_contexts m!i) eta \<longrightarrow>
    SN_on (lp_ild Q) {[(lpcn_pred (lppcm_nodes m!i),map eta (lpcn_vars (lppcm_nodes m!i)))]} \<longrightarrow>
    lp_answer_contract (lpp_integer_answers P) (lpc_return_eval eta (lppcm_states m!i)) (lp_ild Q)
      [(lpcn_pred (lppcm_nodes m!i),map eta (lpcn_vars (lppcm_nodes m!i)))]
      (\<lambda>rho. [(lppcm_returned m,map rho [0..<lppcm_arity m])]))"

lemma lpp_checked_context_data_semantics:
  fixes SP :: "string lpp_success_clause list"
  assumes checked: "lpp_check_context_data fuel P Q T m"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
  shows "lpp_context_data_semantics SP P Q m"
  unfolding lpp_context_data_semantics_def
  using lpp_check_context_module_domain_contract[OF _ transfer _ program]
    checked unfolding lpp_check_context_data_def by blast

lemma lpp_context_semantic_link_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes module: "lpp_context_data_semantics SP P Q m"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
    and link: "lpp_check_context_table_link fuel Q (lppcm_nodes m) (lppcm_states m) (lppcm_contexts m)
      nd ss G guards [] context e"
    and known: "lp_cut_knowledge (set G) guards eta"
    and observed: "lpp_source_context_holds SP context eta"
    and sn: "SN_on (lp_ild Q) {[(lpcn_pred nd,map eta (lpcn_vars nd))]}"
  shows "lp_answer_contract (lpp_integer_answers P) (lpc_return_eval eta ss) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(lppcm_returned m,map rho [0..<lppcm_arity m])])"
proof -
  have equations: "lp_equations [] eta" by (simp add: lp_equations_def)
  obtain u swaps where strict: "([(lpcn_pred nd,map eta (lpcn_vars nd))],u)\<in>(lp_ild Q)\<^sup>+"
    and rep: "lpp_context_return_rep SP (lppcm_nodes m) (lppcm_states m) (lppcm_contexts m)
      (lpc_return_scope_word swaps (lpc_return_eval eta ss)) u"
    using lpp_context_table_link_sound[OF link equations refl known observed] by blast
  obtain j nu where bound: "j<length (lppcm_nodes m)"
    and shape: "lpc_return_scope_word swaps (lpc_return_eval eta ss) = lpc_return_eval nu (lppcm_states m!j)"
    and knowledge: "lp_cut_knowledge (set (lpcn_ground (lppcm_nodes m!j))) (lpcn_guards (lppcm_nodes m!j)) nu"
    and facts: "lpp_source_context_holds SP (lppcm_contexts m!j) nu"
    and u: "u = [(lpcn_pred (lppcm_nodes m!j),map nu (lpcn_vars (lppcm_nodes m!j)))]"
    using rep by (auto simp: lpp_context_return_rep_def)
  have child_sn: "SN_on (lp_ild Q) {u}"
    by (rule SN_on_subset2[OF _ SN_on_Image_rtrancl[OF sn]])
      (use trancl_into_rtrancl[OF strict] in auto)
  have child: "lp_answer_contract (lpp_integer_answers P)
    (lpc_return_eval nu (lppcm_states m!j)) (lp_ild Q) u
    (\<lambda>rho. [(lppcm_returned m,map rho [0..<lppcm_arity m])])"
    using module child_sn bound knowledge facts
    by (auto simp: lpp_context_data_semantics_def u)
  have restored: "lp_answer_contract (lpp_integer_answers P)
    (lpc_return_scope_word (rev swaps) (lpc_return_eval nu (lppcm_states m!j))) (lp_ild Q) u
    (\<lambda>rho. [(lppcm_returned m,map rho [0..<lppcm_arity m])])"
    by (rule lpp_domain_contract_scopes[OF program child])
  have original: "lp_answer_contract (lpp_integer_answers P) (lpc_return_eval eta ss) (lp_ild Q) u
    (\<lambda>rho. [(lppcm_returned m,map rho [0..<lppcm_arity m])])"
    using restored by (simp add: shape[symmetric] lpc_return_scope_word_inverse)
  show ?thesis by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF strict] original])
qed

lemma lpp_context_semantic_continuation:
  fixes SP :: "string lpp_success_clause list"
    and entry :: "string lp_cut_symbol"
  assumes module: "lpp_context_data_semantics SP P Q m"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
    and arity: "lppcm_arity m = length vs"
    and distinct: "distinct vs"
    and indexed: "lpc_return_indexed_goals (length vs) gs"
    and link: "lpp_check_context_table_link fuel Q (lppcm_nodes m) (lppcm_states m) (lppcm_contexts m)
      (lpc_return_bridge_node entry vs)
      [(LPCGoals (lpc_return_named_goals vs gs),map Var vs)] [] [] [] ([],[],[]) e"
    and sn: "SN_on (lp_ild Q) {[(entry,map rho [0..<length vs])]}"
  shows "lp_answer_contract (lpp_integer_answers P)
    [(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t rho)) gs),rho)] (lp_ild Q)
    [(entry,map rho [0..<length vs])] (\<lambda>eta. [(lppcm_returned m,map eta [0..<length vs])])"
proof -
  let ?nu = "lp_cut_query_env vs (map rho [0..<length vs])"
  let ?ss = "[(LPCGoals (map (lp_cut_map (\<lambda>t. lp_ieval t rho)) gs),rho)]"
  let ?F = "lpc_project_interface [0..<length vs]"
  have tuple_values: "map ?nu vs = map rho [0..<length vs]"
    by (rule lp_cut_query_env_values) (use distinct in auto)
  have known: "lp_cut_knowledge (set []) [] ?nu" by (simp add: lp_cut_knowledge_def)
  have observed: "lpp_source_context_holds SP ([],[],[]) ?nu" by (simp add: lpp_path_context_holds_def)
  have residual: "SN_on (lp_ild Q) {[(lpcn_pred (lpc_return_bridge_node entry vs),map ?nu (lpcn_vars (lpc_return_bridge_node entry vs)))]}"
    using sn tuple_values by (simp add: lpc_return_bridge_node_def)
  have contract: "lp_answer_contract (lpp_integer_answers P)
      (lpc_return_eval ?nu [(LPCGoals (lpc_return_named_goals vs gs),map Var vs)]) (lp_ild Q)
      [(entry,map rho [0..<length vs])] (\<lambda>eta. [(lppcm_returned m,map eta [0..<length vs])])"
    using lpp_context_semantic_link_contract[OF module transfer program link known observed residual]
    by (simp add: lpc_return_bridge_node_def tuple_values arity)
  have shape: "lpc_return_eval ?nu [(LPCGoals (lpc_return_named_goals vs gs),map Var vs)] = lpc_reinterface ?F ?ss"
    by (simp add: lpc_return_eval_def lpc_reinterface_def lpc_return_tuple_env[OF distinct]
      lpc_return_named_goals_eval[OF distinct indexed])
  have vector: "map (?F eta) [0..<length vs] = map eta [0..<length vs]" for eta
    by (rule map_cong) (auto simp: lpc_project_interface_def)
  show ?thesis
    apply (rule lpp_domain_contract_lift_interface[where F="?F", OF lpc_project_interface_commutes])
     using contract shape apply simp
    by (simp only: vector; simp)
qed

definition lpp_check_context_split_interface where
  "lpp_check_context_split_interface fuel P Q T nd original context returned arity
      bindings indices pre rest interface pm pe vs cm ce =
    (lpc_check_return_split_shape bindings indices pre rest interface original \<and>
     length indices = arity \<and> length vs = length interface \<and> distinct vs \<and>
     lppcm_arity pm = length vs \<and> lppcm_arity cm = length vs \<and>
     lpc_return_indexed_goals (length vs) (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest) \<and>
     lpp_check_context_table_link fuel Q (lppcm_nodes pm) (lppcm_states pm) (lppcm_contexts pm)
       nd [(LPCGoals pre,interface)] (lpcn_ground nd) (lpcn_guards nd) [] context pe \<and>
     lpp_check_context_table_link fuel Q (lppcm_nodes cm) (lppcm_states cm) (lppcm_contexts cm)
       (lpc_return_bridge_node (lppcm_returned pm) vs)
       [(LPCGoals (lpc_return_named_goals vs (map (lp_cut_map (map_term id (lpc_return_route bindings))) rest)),map Var vs)]
       [] [] [] ([],[],[]) ce \<and>
     lpc_check_return_projection_edge Q vs (lppcm_returned cm) returned indices)"

theorem lpp_context_semantic_split_contract:
  fixes SP :: "string lpp_success_clause list"
  assumes checked: "lpp_check_context_split_interface fuel P Q T nd original context returned arity
      bindings indices pre rest interface pm pe vs cm ce"
    and prefix_module: "lpp_context_data_semantics SP P Q pm"
    and continuation_module: "lpp_context_data_semantics SP P Q cm"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and observed: "lpp_source_context_holds SP context eta"
    and sn: "SN_on (lp_ild Q) {[(lpcn_pred nd,map eta (lpcn_vars nd))]}"
  shows "lp_answer_contract (lpp_integer_answers P) (lpc_return_eval eta original) (lp_ild Q)
    [(lpcn_pred nd,map eta (lpcn_vars nd))] (\<lambda>rho. [(returned,map rho [0..<arity])])"
proof -
  let ?t = "[(lpcn_pred nd,map eta (lpcn_vars nd))]"
  let ?gs = "map (lp_cut_map (map_term id (lpc_return_route bindings))) rest"
  let ?pre = "\<lambda>rho. [(lppcm_returned pm,map rho [0..<length vs])]"
  let ?cont = "\<lambda>rho. [(lppcm_returned cm,map rho [0..<length vs])]"
  have shape: "lpc_check_return_split_shape bindings indices pre rest interface original"
    and arity: "length indices = arity" and distinct: "distinct vs"
    and indexed: "lpc_return_indexed_goals (length vs) ?gs"
    and projection: "lpc_check_return_projection_edge Q vs (lppcm_returned cm) returned indices"
    using checked by (auto simp: lpp_check_context_split_interface_def)
  have pm_arity: "lppcm_arity pm = length vs" using checked by (simp add: lpp_check_context_split_interface_def)
  have prefix: "lp_answer_contract (lpp_integer_answers P)
    (lpc_return_eval eta [(LPCGoals pre,interface)]) (lp_ild Q) ?t ?pre"
    unfolding pm_arity[symmetric]
    by (rule lpp_context_semantic_link_contract[OF prefix_module transfer program _ known observed sn])
      (use checked in \<open>auto simp: lpp_check_context_split_interface_def\<close>)
  have continuation: "lp_answer_contract (lpp_integer_answers P)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) ?gs),rho)] (lp_ild Q) (?pre rho) ?cont"
    if reached: "(?t,?pre rho)\<in>(lp_ild Q)\<^sup>*" for rho
  proof -
    have child_sn: "SN_on (lp_ild Q) {?pre rho}"
      by (rule SN_on_subset2[OF _ SN_on_Image_rtrancl[OF sn]]) (use reached in auto)
    show ?thesis
      by (rule lpp_context_semantic_continuation[OF continuation_module transfer program _ distinct indexed _ child_sn])
        (use checked in \<open>auto simp: lpp_check_context_split_interface_def\<close>)
  qed
  have composed: "lp_answer_contract (lpp_integer_answers P)
    (lpc_attach_answers ?gs (lpc_return_eval eta [(LPCGoals pre,interface)])) (lp_ild Q) ?t ?cont"
    by (rule lpp_domain_contract_compose[OF program prefix])
      (use continuation in \<open>auto simp: lpc_return_eval_def\<close>)
  have bridge: "(?cont rho,[(returned,map (lpc_project_interface indices rho) [0..<arity])])\<in>(lp_ild Q)\<^sup>*" for rho :: "nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
    using lpc_return_projection_edge_sound[OF projection, of rho] arity by auto
  have projected: "lp_answer_contract (lpp_integer_answers P)
    (lpc_reinterface (lpc_project_interface indices)
      (lpc_attach_answers ?gs (lpc_return_eval eta [(LPCGoals pre,interface)]))) (lp_ild Q) ?t
    (\<lambda>rho. [(returned,map rho [0..<arity])])"
    by (rule lpp_domain_contract_project[where F="lpc_project_interface indices", OF lpc_project_interface_commutes composed bridge])
  show ?thesis using projected lpc_return_split_shape_sound[OF shape, of eta] by simp
qed


end
