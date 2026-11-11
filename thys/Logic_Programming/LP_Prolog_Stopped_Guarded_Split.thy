theory LP_Prolog_Stopped_Guarded_Split
 imports LP_Prolog_Stopped_Triple_Prefix LP_Prolog_Stopped_Guarded_Connection LP_Prolog_Stable_Guarded_Split
begin

hide_const (open) Tree_Automata_Containment.entry

theorem lpp_stopped_guarded_child_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
  assumes compatible: "lpp_stable_integer_operations operation"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_finite_triple_check_child T fs fuel roots contexts context pre G guards F vs inp out receipt"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set G) guards eta"
    and observed: "lpp_stable_context_holds operation SP context eta"
    and free: "lpc_free_knowledge (set F) eta"
    and edge: "(a,lp_atom_eval inp eta)\<in>R"
    and lower: "\<And>us b ret. (a,b)\<in>R \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP contexts roots us b ret \<Longrightarrow> lpp_stopped_triple_answer_contract operation P us Q ret"
  shows "lpp_stopped_triple_answer_contract operation P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) Q (lp_atom_eval out)"
proof -
  let ?i = "lpcsh_target receipt"
  let ?entry = "roots!?i"
  let ?nd = "lpctr_node ?entry"
  let ?mu = "lp_cut_instance_subst (lpcsh_bindings receipt)"
  let ?eta = "\<lambda>x. lp_ieval (?mu x) eta"
  have index: "?i<length roots" "?i<length contexts"
    and transport: "lpp_evaluation_context_transport T fs (lpp_context_add_ground context G) (contexts!?i) (lpcsh_bindings receipt)"
    using checked by (auto simp: lpp_finite_triple_check_child_def)
  obtain ce where state: "lpcn_state ?nd=[ce]"
    using checked by (auto simp: lpp_finite_triple_check_child_def Let_def split: list.splits;
      metis list.exhaust)
  have context_ground: "\<forall>x\<in>lpp_source_context_ground context. lp_seg_ground (eta x)"
    by (rule lpp_evaluation_context_ground_sound[OF lpp_finite_evaluation_ground lpp_stable_context_finite_envelope[OF compatible observed]])
  have enriched_known: "lp_cut_knowledge
      (set (G @ filter (\<lambda>x. x\<in>lpp_source_context_ground context) vs)) guards eta"
    using known context_ground by (auto simp: lp_cut_knowledge_def)
  obtain grounded where inst: "lpc_seg_check_instance_boundary (LPCGoals pre) grounded guards vs (map Var vs)
      ce (lpcn_ground ?nd) (lpcn_guards ?nd) (lpcn_vars ?nd)
      (lpcsh_bindings receipt) (lpcsh_swaps receipt)"
    and grounded_known: "lp_cut_knowledge (set grounded) guards eta"
    using checked known enriched_known
    unfolding lpp_finite_triple_check_child_def Let_def state
    by auto
  have free_check: "lpc_check_link_free fuel [] F (lpctr_free ?entry) (lpcsh_bindings receipt)"
    and inp: "lp_atom_subst (lpctr_input ?entry) ?mu=inp"
    and equal: "lpc_triple_observe_atom (map (lpc_seg_position_template vs) (map ?mu (lpcn_vars ?nd)))
      (lpctr_output ?entry) = lpc_triple_observe_atom (map (lpc_seg_position_template vs) (map Var vs)) out"
    using checked by (auto simp: lpp_finite_triple_check_child_def Let_def state)
  have child_known: "lp_cut_knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?eta"
    by (rule lpc_seg_instance_boundary_knowledge[OF inst grounded_known])
  have child_free: "lpc_free_knowledge (set (lpctr_free ?entry)) ?eta"
    by (rule lpc_checked_link_free_sound[OF free_check _ free]) (simp add: lp_equations_def)
  have enriched: "lpp_stable_context_holds operation SP (lpp_context_add_ground context G) eta"
    by (rule lpp_stable_add_ground_sound[OF observed])
      (use known in \<open>auto simp: lp_cut_knowledge_def\<close>)
  have child_context: "lpp_stable_context_holds operation SP (contexts!?i) ?eta"
    by (rule lpp_stable_existing_transport_sound[OF compatible transfer transport enriched])
  have call_eval: "lp_atom_eval inp eta=lp_atom_eval (lpctr_input ?entry) ?eta"
    by (simp add: inp[symmetric] lp_atom_subst_def lp_atom_eval_def lp_ieval_finite_subst map_map o_def)
  have edge': "(a,lp_atom_eval (lpctr_input ?entry) ?eta)\<in>R"
    using edge by (simp only: call_eval)
  have rep: "lpp_stable_triple_root_rep operation SP contexts roots (lpc_return_eval ?eta (lpc_triple_root_state ?entry))
      (lp_atom_eval (lpctr_input ?entry) ?eta) (lp_atom_eval (lpctr_output ?entry))"
    unfolding lpp_stable_triple_root_rep_def
    by (rule exI[of _ ?i], rule exI[of _ ?eta]) (use index child_known child_free child_context in simp)
  have child: "lpp_stopped_triple_answer_contract operation P
      (lpc_return_eval ?eta [(ce,map Var (lpcn_vars ?nd))]) Q (lp_atom_eval (lpctr_output ?entry))"
    using lower[OF edge' rep] by (simp add: lpc_triple_root_state_def state)
  have answer: "lpc_triple_check_instance_answer Q vs (map Var vs) (lpcn_vars ?nd)
      (lpcsh_bindings receipt) (lpctr_output ?entry) out 0 []"
    using equal by (simp add: lpc_triple_check_instance_answer_def)
  show ?thesis by (rule lpp_stopped_triple_checked_instance_contract[OF inst program grounded_known answer child])
qed

theorem lpp_stopped_guarded_split_interface_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts incoming_context outgoing_context entry receipt"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and returns: "\<And>rho. lpp_stopped_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho \<Longrightarrow>
      \<exists>theta. rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<and>
        lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<and>
        lpp_stable_context_holds operation SP outgoing_context theta"
    and first_descent: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)\<in>R"
    and return_descent: "\<And>rho theta. lpp_stopped_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho \<Longrightarrow>
      rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<Longrightarrow>
      lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<Longrightarrow>
      lpp_stable_context_holds operation SP outgoing_context theta \<Longrightarrow>
      (lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_second_in receipt) theta)\<in>R"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>R \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP contexts roots us b ret \<Longrightarrow> lpp_stopped_triple_answer_contract operation P us Q ret"
  shows "lpp_stopped_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
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
  have prefix: "lpp_stopped_triple_answer_contract operation P ?ss Q (lp_atom_eval ?fo)"
    by (rule lpp_stopped_guarded_child_checked_lower[OF compatible transfer first program known observed free first_descent lower])
  have equal: "lp_atom_eval ?inp (lpc_return_env (map Var ?vs) eta)=?a"
    by (rule lpc_triple_position_atom_eval[OF distinct input_vars])
  have inv: "lpc_triple_instance_invariant ?a ?inp ?ss"
    unfolding lpc_triple_instance_invariant_def lpc_return_eval_def
    by (auto simp: equal intro!: exI[of _ LPIVar])
  have composed: "lpp_stopped_triple_answer_contract operation P (lpc_attach_answers ?routed ?ss) Q (lp_atom_eval (lpctr_output entry))"
  proof (rule lpp_stopped_triple_split_checked_continuation[OF program prefix inv _ _ middle success])
    show "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ?ss"
      using nonempty by (simp add: lpc_return_eval_def)
    show "lpc_rest_scopes ?routed \<inter> set (lpc_barrier_ids (map fst ?ss))={}"
      by (simp add: lpc_return_eval_def)
  next
    fix rho assume actual: "lpp_stopped_actual_return operation P ?ss rho"
      and edge: "(?a,lp_atom_eval (lpc_triple_position_atom ?vs ?si) rho)\<in>lp_triple_calls (set D) Q"
    obtain theta where rho: "rho=lpc_return_env (map Var ?vs) theta"
      and child_known: "lp_cut_knowledge (set ?H) [] theta"
      and next_context: "lpp_stable_context_holds operation SP outgoing_context theta"
      using returns[OF actual] by blast
    have descent: "(?a,lp_atom_eval ?si theta)\<in>R"
      by (rule return_descent[OF actual rho child_known next_context])
    have child: "lpp_stopped_triple_answer_contract operation P
      (lpc_return_eval theta [(LPCGoals ?rest,map Var ?vs)]) Q (lp_atom_eval ?so)"
      by (rule lpp_stopped_guarded_child_checked_lower[OF compatible transfer second program child_known next_context _ descent lower])
        (simp add: lpc_free_knowledge_def)
    have source_equal: "[(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) ?routed),rho)] =
      lpc_return_eval theta [(LPCGoals ?rest,map Var ?vs)]"
      using lpc_return_route_goals[OF route, of theta] by (simp add: rho lpc_return_eval_def)
    show "lpp_stopped_triple_answer_contract operation P
      [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) ?routed),rho)] Q (lp_atom_eval ?so)"
      using child by (simp only: source_equal)
  qed
  have shape: "lpc_attach_answers ?routed ?ss=lpc_return_eval eta (lpc_triple_root_state entry)"
    using lpc_return_route_goals[OF route, of eta]
    by (simp add: lpc_triple_root_state_def state lpc_return_eval_def lpc_attach_answers_def)
  show ?thesis using composed by (simp only: shape)
qed
ML \<open>
val checked = [@{thm lpp_stopped_guarded_child_checked_lower}, @{thm lpp_stopped_guarded_split_interface_lower}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stopped guarded Split dependency" else ();
\<close>
end
