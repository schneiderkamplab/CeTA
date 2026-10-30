theory LP_Prolog_Triple_Split_Interface
 imports LP_Prolog_Triple_Child LP_Prolog_Triple_Split LP_Prolog_Actual_Contexts
   LP_Cut_SEG_Triple_Split_Check
begin

hide_const (open) Tree_Automata_Containment.entry

definition lpp_triple_check_split_interface where
  "lpp_triple_check_split_interface fuel D Q roots contexts incoming_context outgoing_context entry receipt =
    (let nd=lpctr_node entry; vs=lpcn_vars nd; G=lpcn_ground nd;
      pre=lpcts_pre receipt; rest=lpcts_rest receipt; H=lpcts_ground receipt;
      fi=lpcts_first_in receipt; fo=lpcts_first_out receipt;
      si=lpcts_second_in receipt; so=lpcts_second_out receipt;
      dc=lpcts_first_call receipt; ec=lpcts_second_call receipt; pc=lpcts_success receipt in
      lpcn_state nd=[LPCGoals (pre@rest)] \<and> pre\<noteq>[] \<and> distinct vs \<and>
      set (lp_atom_vars (lpctr_input entry)) \<subseteq> set vs \<and>
      set (lp_atom_vars si) \<subseteq> set vs \<and> set H \<subseteq> set vs \<and>
      lpc_check_return_route_goals (zip vs [0..<length vs]) (map Var vs :: (string lp_cut_symbol,string) term list) rest \<and>
      lpp_triple_check_child fuel roots contexts incoming_context pre G (lpcn_guards nd) (lpctr_free entry) vs fi fo (lpcts_first receipt) \<and>
      lpp_triple_check_child fuel roots contexts outgoing_context rest H [] [] vs si so (lpcts_second receipt) \<and>
      lpc_triple_check_call D [] (lpctr_input entry) fi (fst dc) (snd dc) \<and>
      lpc_triple_check_call D [fo] (lpc_triple_position_atom vs (lpctr_input entry))
        (lpc_triple_position_atom vs si) (fst ec) (snd ec) \<and>
      lpc_triple_check_model_clause Q [so,fo] (lpctr_output entry) (fst pc) (snd pc))"

theorem lpp_triple_split_interface_lower:
  fixes P :: "(string,string) lp_cut_program"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpp_triple_check_split_interface fuel D Q roots contexts incoming_context outgoing_context entry receipt"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and observed: "lpp_source_context_holds SP incoming_context eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and returns: "\<And>rho. lpp_actual_return P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho \<Longrightarrow>
      \<exists>theta. rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<and>
        lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<and>
        lpp_source_context_holds SP outgoing_context theta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      lpp_triple_root_rep SP contexts roots us b ret \<Longrightarrow> lpp_triple_answer_contract P us Q ret"
  shows "lpp_triple_answer_contract P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
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
    and first: "lpp_triple_check_child fuel roots contexts incoming_context ?pre ?G (lpcn_guards ?nd) (lpctr_free entry) ?vs ?fi ?fo (lpcts_first receipt)"
    and second: "lpp_triple_check_child fuel roots contexts outgoing_context ?rest ?H [] [] ?vs ?si ?so (lpcts_second receipt)"
    and enter: "lpc_triple_check_call D [] (lpctr_input entry) ?fi
      (fst (lpcts_first_call receipt)) (snd (lpcts_first_call receipt))"
    and middle: "lpc_triple_check_call D [?fo] ?inp (lpc_triple_position_atom ?vs ?si)
      (fst (lpcts_second_call receipt)) (snd (lpcts_second_call receipt))"
    and success: "lpc_triple_check_model_clause Q [?so,?fo] (lpctr_output entry)
      (fst (lpcts_success receipt)) (snd (lpcts_success receipt))"
    using checked by (auto simp: lpp_triple_check_split_interface_def lpc_seg_ground_evidence_check_def Let_def)
  have first_edge: "(?a,lp_atom_eval ?fi eta)\<in>lp_triple_calls (set D) Q"
    by (rule lpc_triple_checked_call[OF enter, where sigma=LPIVar]) simp_all
  have prefix: "lpp_triple_answer_contract P ?ss Q (lp_atom_eval ?fo)"
    by (rule lpp_triple_child_checked_lower[OF first program known observed free first_edge lower])
  have equal: "lp_atom_eval ?inp (lpc_return_env (map Var ?vs) eta)=?a"
    by (rule lpc_triple_position_atom_eval[OF distinct input_vars])
  have inv: "lpc_triple_instance_invariant ?a ?inp ?ss"
    unfolding lpc_triple_instance_invariant_def lpc_return_eval_def
    by (auto simp: equal intro!: exI[of _ LPIVar])
  have composed: "lpp_triple_answer_contract P (lpc_attach_answers ?routed ?ss) Q (lp_atom_eval (lpctr_output entry))"
  proof (rule lpp_triple_split_checked_continuation[OF program prefix inv _ _ middle success])
    show "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ?ss"
      using nonempty by (simp add: lpc_return_eval_def)
    show "lpc_rest_scopes ?routed \<inter> set (lpc_barrier_ids (map fst ?ss))={}"
      by (simp add: lpc_return_eval_def)
  next
    fix rho assume actual: "lpp_actual_return P ?ss rho"
      and edge: "(?a,lp_atom_eval (lpc_triple_position_atom ?vs ?si) rho)\<in>lp_triple_calls (set D) Q"
    obtain theta where rho: "rho=lpc_return_env (map Var ?vs) theta"
      and child_known: "lp_cut_knowledge (set ?H) [] theta"
      and next_context: "lpp_source_context_holds SP outgoing_context theta"
      using returns[OF actual] by blast
    have edge': "(?a,lp_atom_eval ?si theta)\<in>lp_triple_calls (set D) Q"
      using edge by (simp only: rho lpc_triple_position_atom_eval[OF distinct next_vars])
    have child: "lpp_triple_answer_contract P
      (lpc_return_eval theta [(LPCGoals ?rest,map Var ?vs)]) Q (lp_atom_eval ?so)"
      by (rule lpp_triple_child_checked_lower[OF second program child_known next_context _ edge' lower])
        (simp add: lpc_free_knowledge_def)
    have source_equal: "[(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) ?routed),rho)] =
      lpc_return_eval theta [(LPCGoals ?rest,map Var ?vs)]"
      using lpc_return_route_goals[OF route, of theta] by (simp add: rho lpc_return_eval_def)
    show "lpp_triple_answer_contract P
      [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) ?routed),rho)] Q (lp_atom_eval ?so)"
      using child by (simp only: source_equal)
  qed
  have shape: "lpc_attach_answers ?routed ?ss=lpc_return_eval eta (lpc_triple_root_state entry)"
    using lpc_return_route_goals[OF route, of eta]
    by (simp add: lpc_triple_root_state_def state lpc_return_eval_def lpc_attach_answers_def)
  show ?thesis using composed by (simp only: shape)
qed

end
