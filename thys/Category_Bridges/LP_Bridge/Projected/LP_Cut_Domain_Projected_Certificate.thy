theory LP_Cut_Domain_Projected_Certificate
 imports LP_Cut_Domain_Projected_Nested
begin
hide_const (open) CPF_Proof_Parser.rstep

context cut_runtime_domain
begin
theorem precise_projected_root_sound:
  fixes ts :: "('f lp_cut_symbol,string) term list"
  assumes checked: "lpc_projected_check_root fuel k P filtering R Q modules actions m r q modes"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
    and child: "SN (rstep (af_rule filtering ` set R))"
  shows "SN_on (precise_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof -
  let ?nd = "lpcrm_nodes (modules!m)!r"
  let ?vs = "lpcn_vars ?nd"
  let ?vals = "map (\<lambda>t. lp_ieval t LPIVar) ts"
  let ?env = "lp_cut_query_env ?vs ?vals"
  have root: "lp_cut_check_root q modes ?vs (lpcn_state ?nd) (lpcn_ground ?nd) (lpcn_guards ?nd)"
    and table: "lpc_check_projected_nested fuel k P filtering R Q modules actions m" and bound: "r<length (lpcrm_nodes (modules!m))"
    and program: "lp_cut_source_program P"
    using checked by (auto simp: lpc_projected_check_root_def)
  have lengths: "length ?vs=length ?vals" and distinct: "distinct ?vs"
    using root len by (auto simp: lp_cut_check_root_def)
  have vals: "map ?env ?vs=?vals" by (rule lp_cut_query_env_values[OF lengths distinct])
  have finite_index: "\<And>i. i<length modes \<Longrightarrow> modes!i \<Longrightarrow> lp_seg_ground (?vals!i)"
    using ground len by (auto simp: lpc_positions_def lp_seg_ground_eval ground_vars_term_empty)
  have finite: "\<forall>(t,b)\<in>set (zip ?vals modes). b \<longrightarrow> lp_seg_ground t"
    using finite_index len by (auto simp: in_set_zip)
  have finite': "\<forall>(t,b)\<in>set (zip (map ?env ?vs) modes). b \<longrightarrow> lp_seg_ground t"
    using finite by (simp only: vals)
  have envD: "\<forall>x. D (?env x)"
    by (intro allI; rule query_env_domain) (auto intro: valuation_domain variables)
  have known: "knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?env"
    using root finite' envD by (auto simp: lp_cut_check_root_def knowledge_def zip_map1)
  have query: "lp_check_query filtering (lpcn_pred ?nd) (length modes) (lpc_positions modes)"
    using checked by (simp add: lpc_projected_check_root_def)
  obtain x :: "('f lp_cut_symbol,string) term" where pr:
    "lp_iproject filtering (LPIFun (lpcn_pred ?nd) ?vals) x"
    using lp_check_query_infinite_projection[OF query, of ?vals id] finite_index len
    by (auto simp: lpc_positions_def lp_iterm.map_id o_def)
  have obs: "lpc_observes filtering [(lpcn_pred ?nd,map ?env ?vs)] x"
    using pr vals by (simp add: lpc_observes_def)
  have observed: "lpc_observed filtering [(lpcn_pred ?nd,map ?env ?vs)]"
    using obs by (auto simp: lpc_observed_def)
  have residual: "SN_on (lpc_projected_rel filtering (set R)) {[(lpcn_pred ?nd,map ?env ?vs)]}"
    by (rule lpc_projected_rel_SN[OF SN_on_subset2[OF _ child] obs]) auto
  have contract: "precise_return_contract P (lpc_return_eval ?env (lpcrm_states (modules!m)!r)) (lpc_projected_rel filtering (set R))
    [(lpcn_pred ?nd,map ?env ?vs)] (\<lambda>rho. [(lpcrm_returned (modules!m),map rho [0..<lpcrm_arity (modules!m)])])"
    by (rule precise_projected_semantic_dataD[OF precise_check_projected_nested_sound[OF table program] bound known observed residual])
  have state: "map fst (lpcrm_states (modules!m)!r)=lpcn_state ?nd"
    using table bound by (cases k) (auto simp: Let_def list_all_iff)
  have source: "SN_on (precise_source P) {lp_cut_state_eval (lpcn_state ?nd) ?env}"
    using contract by (simp add: precise_return_contract_def lpc_return_eval_erases state)
  show ?thesis using source root vals
    by (simp add: lp_cut_check_root_def lp_cut_state_map_def map_map o_def)
qed



end
context
  fixes D :: "(string lp_cut_symbol,string) lp_iterm \<Rightarrow> bool"
  assumes domain: "cut_runtime_domain D"
begin
interpretation cut_runtime_domain D by (rule domain)
theorem precise_projected_certificate_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and checked: "check_lpc_projected_certificate I J rename fuel k P filters R Q modules actions m r q modes prf"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (precise_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof -
  interpret tp_spec I by (rule I)
  obtain filtering where filter: "afs_of filters=Some filtering"
    using checked unfolding check_lpc_projected_certificate_def
    by (cases "afs_of filters") auto
  have root: "lpc_projected_check_root fuel k P filtering R Q modules actions m r q modes"
    and child_proof: "isOK (check_trs_termination_proof I J False id
      (tp_ops.mk I False [] (map (map_funs_rule rename) (map (af_rule filtering) R)) []) prf)"
    using checked by (auto simp: check_lpc_projected_certificate_def filter)
  have mapped: "SN (rstep (map_funs_trs rename (set (map (af_rule filtering) R))))"
    using check_trs_termination_proof[OF I J child_proof]
      by (simp add: SN_qrel_def map_prod_def image_image map_funs_trs.simps map_funs_rule.simps split_def)
  have sn: "SN (rstep (set (map (af_rule filtering) R)))"
  proof -
    have each: "SN_on (rstep (set (map (af_rule filtering) R))) {t}" for t
      by (rule SN_map_imp_SN[where fg=rename])
        (rule SN_on_subset2[OF _ mapped], simp)
    show ?thesis using each unfolding SN_on_def by blast
  qed
  show ?thesis by (rule precise_projected_root_sound[OF root len ground sn[simplified]])
qed


end
end
