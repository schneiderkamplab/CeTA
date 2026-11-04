theory LP_Prolog_Finite_Guarded_Split
 imports LP_Prolog_Finite_Triple_Split_Interface LP_Prolog_Finite_Guarded_Child
begin

hide_const (open) Tree_Automata_Containment.entry

text \<open>Both calls of the established Split must descend in the chosen
relation. Continuation descent is conditional on an actual successful prefix
return and its checked context. Abstract residual success values alone cannot
discharge this premise. The source execution and return composition are shared
with the finite triple checker.\<close>

theorem lpp_finite_guarded_split_interface_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts incoming_context outgoing_context entry receipt"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming_context eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and returns: "\<And>rho. lpp_finite_actual_return P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho \<Longrightarrow>
      \<exists>theta. rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<and>
        lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<and>
        lpp_evaluation_context_holds lpp_finite_evaluation_result SP outgoing_context theta"
    and first_descent: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)\<in>R"
    and return_descent: "\<And>rho theta. lpp_finite_actual_return P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho \<Longrightarrow>
      rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<Longrightarrow>
      lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<Longrightarrow>
      lpp_evaluation_context_holds lpp_finite_evaluation_result SP outgoing_context theta \<Longrightarrow>
      (lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_second_in receipt) theta)\<in>R"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>R \<Longrightarrow>
      lpp_finite_triple_root_rep SP contexts roots us b ret \<Longrightarrow> lpp_finite_triple_answer_contract P us Q ret"
  shows "lpp_finite_triple_answer_contract P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
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
    and route: "lpc_check_return_route_goals (zip ?vs [0..<length ?vs]) (map Var ?vs :: (string lp_cut_symbol,string) term list) ?rest"
    and first: "lpp_finite_triple_check_child T first_types fuel roots contexts incoming_context ?pre ?G (lpcn_guards ?nd) (lpctr_free entry) ?vs ?fi ?fo (lpcts_first receipt)"
    and second: "lpp_finite_triple_check_child T second_types fuel roots contexts outgoing_context ?rest ?H [] [] ?vs ?si ?so (lpcts_second receipt)"
    and enter: "lpc_triple_check_call D [] (lpctr_input entry) ?fi
      (fst (lpcts_first_call receipt)) (snd (lpcts_first_call receipt))"
    and middle: "lpc_triple_check_call D [?fo] ?inp (lpc_triple_position_atom ?vs ?si)
      (fst (lpcts_second_call receipt)) (snd (lpcts_second_call receipt))"
    and success: "lpc_triple_check_model_clause Q [?so,?fo] (lpctr_output entry)
      (fst (lpcts_success receipt)) (snd (lpcts_success receipt))"
    using checked by (auto simp: lpp_finite_triple_check_split_interface_def lpc_seg_ground_evidence_check_def Let_def)
  have prefix: "lpp_finite_triple_answer_contract P ?ss Q (lp_atom_eval ?fo)"
    by (rule lpp_finite_guarded_child_checked_lower[OF transfer first program known observed free first_descent lower])
  have equal: "lp_atom_eval ?inp (lpc_return_env (map Var ?vs) eta)=?a"
    by (rule lpc_triple_position_atom_eval[OF distinct input_vars])
  have inv: "lpc_triple_instance_invariant ?a ?inp ?ss"
    unfolding lpc_triple_instance_invariant_def lpc_return_eval_def
    by (auto simp: equal intro!: exI[of _ LPIVar])
  have composed: "lpp_finite_triple_answer_contract P (lpc_attach_answers ?routed ?ss) Q (lp_atom_eval (lpctr_output entry))"
  proof (rule lpp_finite_triple_split_checked_continuation[OF program prefix inv _ _ middle success])
    show "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ?ss"
      using nonempty by (simp add: lpc_return_eval_def)
    show "lpc_rest_scopes ?routed \<inter> set (lpc_barrier_ids (map fst ?ss))={}"
      by (simp add: lpc_return_eval_def)
  next
    fix rho assume actual: "lpp_finite_actual_return P ?ss rho"
      and edge: "(?a,lp_atom_eval (lpc_triple_position_atom ?vs ?si) rho)\<in>lp_triple_calls (set D) Q"
    obtain theta where rho: "rho=lpc_return_env (map Var ?vs) theta"
      and child_known: "lp_cut_knowledge (set ?H) [] theta"
      and next_context: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP outgoing_context theta"
      using returns[OF actual] by blast
    have descent: "(?a,lp_atom_eval ?si theta)\<in>R"
      by (rule return_descent[OF actual rho child_known next_context])
    have child: "lpp_finite_triple_answer_contract P
      (lpc_return_eval theta [(LPCGoals ?rest,map Var ?vs)]) Q (lp_atom_eval ?so)"
      by (rule lpp_finite_guarded_child_checked_lower[OF transfer second program child_known next_context _ descent lower])
        (simp add: lpc_free_knowledge_def)
    have source_equal: "[(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) ?routed),rho)] =
      lpc_return_eval theta [(LPCGoals ?rest,map Var ?vs)]"
      using lpc_return_route_goals[OF route, of theta] by (simp add: rho lpc_return_eval_def)
    show "lpp_finite_triple_answer_contract P
      [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) ?routed),rho)] Q (lp_atom_eval ?so)"
      using child by (simp only: source_equal)
  qed
  have shape: "lpc_attach_answers ?routed ?ss=lpc_return_eval eta (lpc_triple_root_state entry)"
    using lpc_return_route_goals[OF route, of eta]
    by (simp add: lpc_triple_root_state_def state lpc_return_eval_def lpc_attach_answers_def)
  show ?thesis using composed by (simp only: shape)
qed

ML \<open>
val checked = [@{thm lpp_finite_guarded_split_interface_lower}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted finite guarded Split" else ();
\<close>
end
