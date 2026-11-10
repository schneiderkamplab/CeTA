theory LP_Cut_Domain_SEG_Triple_Split_Check
 imports LP_Cut_Domain_SEG_Triple_Split
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_triple_split_checked_lower:
  fixes entry
    and P :: "('f,string) lp_cut_program"
    and eta :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpc_triple_check_split fuel P triples Q roots entry receipt"
    and program: "lp_cut_source_program P"
    and known: "knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>lp_triple_calls (set triples) Q \<Longrightarrow>
      precise_triple_root_rep roots us b ret \<Longrightarrow> precise_triple_answer_contract P us Q ret"
  shows "precise_triple_answer_contract P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof -
  let ?nd = "lpctr_node entry"
  let ?vs = "lpcn_vars ?nd"
  let ?G = "lpcn_ground ?nd"
  let ?H = "lpcts_ground receipt"
  let ?pre = "lpcts_pre receipt"
  let ?rest = "lpcts_rest receipt"
  let ?ss = "lpc_return_eval eta [(LPCGoals ?pre,map Var ?vs)]"
  let ?routed = "map (lp_cut_map (map_term id (lpc_return_route (zip ?vs [0..<length ?vs])))) ?rest"
  let ?a = "lp_atom_eval (lpctr_input entry) eta"
  let ?inp = "lpc_triple_position_atom ?vs (lpctr_input entry)"
  let ?fi = "lpcts_first_in receipt"
  let ?fo = "lpcts_first_out receipt"
  let ?si = "lpcts_second_in receipt"
  let ?so = "lpcts_second_out receipt"
  have state: "lpcn_state ?nd=[LPCGoals (?pre@?rest)]"
    and nonempty: "?pre\<noteq>[]" and distinct: "distinct ?vs"
    and input_vars: "set (lp_atom_vars (lpctr_input entry)) \<subseteq> set ?vs"
    and next_vars: "set (lp_atom_vars ?si) \<subseteq> set ?vs"
    and ground_vars: "set ?H \<subseteq> set ?vs"
    and route: "lpc_check_return_route_goals (zip ?vs [0..<length ?vs]) (map Var ?vs :: ('f lp_cut_symbol,string) term list) ?rest"
    and first: "lpc_triple_check_child fuel roots ?pre ?G (lpcn_guards ?nd) (lpctr_free entry) ?vs ?fi ?fo (lpcts_first receipt)"
    and second: "lpc_triple_check_child fuel roots ?rest ?H [] [] ?vs ?si ?so (lpcts_second receipt)"
    and enter: "lpc_triple_check_call triples [] (lpctr_input entry) ?fi
      (fst (lpcts_first_call receipt)) (snd (lpcts_first_call receipt))"
    and middle: "lpc_triple_check_call triples [?fo] ?inp (lpc_triple_position_atom ?vs ?si)
      (fst (lpcts_second_call receipt)) (snd (lpcts_second_call receipt))"
    and success: "lpc_triple_check_model_clause Q [?so,?fo] (lpctr_output entry)
      (fst (lpcts_success receipt)) (snd (lpcts_success receipt))"
    and ground_check: "lpc_seg_check_return_ground P ?pre ?G ?vs (Fun LPCTruth (map Var ?H))
      (lpcsk_program (lpcts_ground_evidence receipt))
      (lpcsk_predicates (lpcts_ground_evidence receipt)) (lpcsk_modes (lpcts_ground_evidence receipt))"
    using checked by (auto simp: lpc_triple_check_split_def lpc_seg_ground_evidence_check_def Let_def)
  have first_edge: "(?a,lp_atom_eval ?fi eta)\<in>lp_triple_calls (set triples) Q"
    by (rule lpc_triple_checked_call[OF enter, where sigma=LPIVar]) simp_all
  have prefix: "precise_triple_answer_contract P ?ss Q (lp_atom_eval ?fo)"
    by (rule precise_triple_child_checked_lower[OF first program known free first_edge lower])
  have equal: "lp_atom_eval ?inp (lpc_return_env (map Var ?vs) eta)=?a"
    by (rule lpc_triple_position_atom_eval[OF distinct input_vars])
  have inv: "lpc_triple_instance_invariant ?a ?inp ?ss"
    unfolding lpc_triple_instance_invariant_def lpc_return_eval_def
    by (auto simp: equal intro!: exI[of _ LPIVar])
  have composed: "precise_triple_answer_contract P (lpc_attach_answers ?routed ?ss) Q (lp_atom_eval (lpctr_output entry))"
  proof (rule precise_triple_split_checked_continuation[OF program prefix inv _ _ middle success])
    show "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ?ss"
      using nonempty by (simp add: lpc_return_eval_def)
    show "lpc_rest_scopes ?routed \<inter> set (lpc_barrier_ids (map fst ?ss))={}"
      by (simp add: lpc_return_eval_def)
  next
    fix rho assume actual: "precise_actual_return P ?ss rho"
      and edge: "(?a,lp_atom_eval (lpc_triple_position_atom ?vs ?si) rho)\<in>lp_triple_calls (set triples) Q"
    obtain theta where source: "precise_actual_return P
        [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) (LPCGoals ?pre),eta)] theta"
      and rho: "rho=lpc_return_env (map Var ?vs) theta"
      using precise_seg_observed_actual[OF actual] by blast
    have initial: "precise_environments [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) (LPCGoals ?pre),eta)]"
      using knowledge_domain[OF known] by (simp add: precise_environments_def)
    have thetaD: "\<And>x. D (theta x)"
      by (rule precise_actual_return_domain[OF initial source])
    have gr: "\<forall>x\<in>set ?G. lp_seg_ground (eta x)"
      using known by (simp add: knowledge_def)
    have child_ground: "\<forall>x\<in>set ?H. lp_seg_ground (theta x)"
      by (rule precise_seg_return_ground_environment[OF ground_check gr actual distinct ground_vars rho])
    have child_known: "knowledge (set ?H) [] theta"
      using child_ground thetaD by (simp add: knowledge_def)
    have edge': "(?a,lp_atom_eval ?si theta)\<in>lp_triple_calls (set triples) Q"
      using edge by (simp only: rho lpc_triple_position_atom_eval[OF distinct next_vars])
    have child: "precise_triple_answer_contract P
      (lpc_return_eval theta [(LPCGoals ?rest,map Var ?vs)]) Q (lp_atom_eval ?so)"
      by (rule precise_triple_child_checked_lower[OF second program child_known _ edge' lower])
        (simp add: lpc_free_knowledge_def)
    have source_equal: "[(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) ?routed),rho)] =
      lpc_return_eval theta [(LPCGoals ?rest,map Var ?vs)]"
      using lpc_return_route_goals[OF route, of theta] by (simp add: rho lpc_return_eval_def)
    show "precise_triple_answer_contract P
      [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) ?routed),rho)] Q (lp_atom_eval ?so)"
      using child by (simp only: source_equal)
  qed
  have shape: "lpc_attach_answers ?routed ?ss=lpc_return_eval eta (lpc_triple_root_state entry)"
    using lpc_return_route_goals[OF route, of eta]
    by (simp add: lpc_triple_root_state_def state lpc_return_eval_def lpc_attach_answers_def)
  show ?thesis using composed by (simp only: shape)
qed


end
end
