theory LP_Prolog_Finite_Local_Return_Families
 imports LP_Prolog_Stable_Guarded_Returns LP_Prolog_Finite_Local_Returns
begin
hide_const (open) Tree_Automata_Containment.entry

text \<open>Reuse the existing independently checked actual-return receipts.
Integer, ground and combined shape contracts justify the continuation context;
the guarded call relation must separately cover both Split dependencies.\<close>

theorem lpp_finite_local_integer_split_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_finite_triple_check_integer_split T first_types second_types fuel P D Q roots contexts incoming_context entry receipt evidence"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and finite: "lpp_finite_direct_invariant A (lpc_return_eval eta (lpc_triple_root_state entry))"
    and continuation: "lpp_check_finite_return_goals A
      (lpcts_ground receipt @ filter (\<lambda>x. x\<in>lpp_source_context_ground (lpp_context_add_integers incoming_context (lppsir_integers evidence)))
        (lpcn_vars (lpctr_node entry))) (lpcts_rest receipt)"
    and first_descent: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)\<in>R"
    and return_descent: "\<And>rho theta. lpp_stable_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho \<Longrightarrow>
      rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<Longrightarrow>
      lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<Longrightarrow>
      lpp_stable_context_holds operation SP (lpp_context_add_integers incoming_context (lppsir_integers evidence)) theta \<Longrightarrow>
      (lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_second_in receipt) theta)\<in>R"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>R \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP contexts roots us b ret \<Longrightarrow> lpp_finite_direct_invariant A us \<Longrightarrow> lpp_stable_triple_answer_contract operation P us Q ret"
  shows "lpp_stable_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof -
  have interface: "lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts incoming_context
    (lpp_context_add_integers incoming_context (lppsir_integers evidence)) entry receipt"
    and returns: "lpp_finite_integer_receipt_check P incoming_context (lpcts_pre receipt)
      (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt) (lpcn_vars (lpctr_node entry)) evidence"
    using checked by (auto simp: lpp_finite_triple_check_integer_split_def)
  show ?thesis by (rule lpp_finite_local_ground_split_interface_lower[OF compatible transfer interface program known observed free finite continuation
    lpp_stable_integer_receipt_return[OF compatible returns known observed] first_descent return_descent lower])
qed

theorem lpp_finite_local_ground_split_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_finite_triple_check_ground_split T first_types second_types fuel P D Q roots contexts incoming_context entry receipt evidence"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and finite: "lpp_finite_direct_invariant A (lpc_return_eval eta (lpc_triple_root_state entry))"
    and continuation: "lpp_check_finite_return_goals A
      (lpcts_ground receipt @ filter (\<lambda>x. x\<in>lpp_source_context_ground (lpp_context_add_ground incoming_context (lppsgr_ground evidence)))
        (lpcn_vars (lpctr_node entry))) (lpcts_rest receipt)"
    and first_descent: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)\<in>R"
    and return_descent: "\<And>rho theta. lpp_stable_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho \<Longrightarrow>
      rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<Longrightarrow>
      lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<Longrightarrow>
      lpp_stable_context_holds operation SP (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) theta \<Longrightarrow>
      (lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_second_in receipt) theta)\<in>R"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>R \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP contexts roots us b ret \<Longrightarrow> lpp_finite_direct_invariant A us \<Longrightarrow> lpp_stable_triple_answer_contract operation P us Q ret"
  shows "lpp_stable_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof -
  have interface: "lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts incoming_context
    (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) entry receipt"
    and returns: "lpp_finite_ground_receipt_check P incoming_context (lpcts_pre receipt)
      (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt) (lpcn_vars (lpctr_node entry)) evidence"
    using checked by (auto simp: lpp_finite_triple_check_ground_split_def)
  show ?thesis by (rule lpp_finite_local_ground_split_interface_lower[OF compatible transfer interface program known observed free finite continuation
    lpp_stable_ground_receipt_return[OF compatible returns known observed] first_descent return_descent lower])
qed

theorem lpp_finite_local_shape_split_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_finite_triple_check_shape_split T first_types second_types fuel P D Q roots contexts incoming_context entry receipt evidence"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and finite: "lpp_finite_direct_invariant A (lpc_return_eval eta (lpc_triple_root_state entry))"
    and continuation: "lpp_check_finite_return_goals A
      (lpcts_ground receipt @ filter (\<lambda>x. x\<in>lpp_source_context_ground (lpp_shape_receipt_context incoming_context evidence))
        (lpcn_vars (lpctr_node entry))) (lpcts_rest receipt)"
    and first_descent: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)\<in>R"
    and return_descent: "\<And>rho theta. lpp_stable_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho \<Longrightarrow>
      rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<Longrightarrow>
      lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<Longrightarrow>
      lpp_stable_context_holds operation SP (lpp_shape_receipt_context incoming_context evidence) theta \<Longrightarrow>
      (lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_second_in receipt) theta)\<in>R"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>R \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP contexts roots us b ret \<Longrightarrow> lpp_finite_direct_invariant A us \<Longrightarrow> lpp_stable_triple_answer_contract operation P us Q ret"
  shows "lpp_stable_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof -
  have interface: "lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts incoming_context
    (lpp_shape_receipt_context incoming_context evidence) entry receipt"
    and returns: "lpp_finite_shape_receipt_check P incoming_context (lpcts_pre receipt)
      (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt) (lpcn_vars (lpctr_node entry)) evidence"
    using checked by (auto simp: lpp_finite_triple_check_shape_split_def)
  show ?thesis by (rule lpp_finite_local_ground_split_interface_lower[OF compatible transfer interface program known observed free finite continuation
    lpp_stable_shape_receipt_return[OF compatible returns known observed] first_descent return_descent lower])
qed

theorem lpp_finite_local_preserved_split_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_finite_triple_check_preserved_split T first_types second_types fuel D Q roots contexts incoming_context entry receipt"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and finite: "lpp_finite_direct_invariant A (lpc_return_eval eta (lpc_triple_root_state entry))"
    and continuation: "lpp_check_finite_return_goals A
      (lpcts_ground receipt @ filter (\<lambda>x. x\<in>lpp_source_context_ground incoming_context)
        (lpcn_vars (lpctr_node entry))) (lpcts_rest receipt)"
    and first_descent: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)\<in>R"
    and return_descent: "\<And>rho theta. lpp_stable_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho \<Longrightarrow>
      rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<Longrightarrow>
      lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<Longrightarrow>
      lpp_stable_context_holds operation SP incoming_context theta \<Longrightarrow>
      (lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_second_in receipt) theta)\<in>R"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>R \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP contexts roots us b ret \<Longrightarrow> lpp_finite_direct_invariant A us \<Longrightarrow> lpp_stable_triple_answer_contract operation P us Q ret"
  shows "lpp_stable_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof -
  have interface: "lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts
      incoming_context incoming_context entry receipt"
    and subset: "set (lpcts_ground receipt) \<subseteq> set (lpcn_ground (lpctr_node entry))"
    using checked by (auto simp: lpp_finite_triple_check_preserved_split_def)
  show ?thesis
  proof (rule lpp_finite_local_ground_split_interface_lower[OF compatible transfer interface program known observed free finite continuation _ first_descent return_descent lower])
    fix rho
    assume actual: "lpp_stable_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho"
    obtain theta where source: "lpp_stable_actual_return operation P
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) (LPCGoals (lpcts_pre receipt)),eta)] theta"
      and rho: "rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta"
      using lpp_stable_seg_observed_actual[OF actual] by blast
    have preserved: "lpp_stable_context_holds operation SP incoming_context theta"
      by (rule lpp_stable_actual_return_preserves_context[OF source]) (use observed in simp)
    have ground: "lp_seg_ground (theta x)" if x: "x\<in>set (lpcts_ground receipt)" for x
    proof -
      have finite: "lp_seg_ground (eta x)" using known subset x by (auto simp: lp_cut_knowledge_def)
      have "theta x=eta x"
        using lpp_actual_return_preserves_finite_value[OF finite source, of x] by simp
      then show ?thesis using finite by simp
    qed
    show "\<exists>theta. rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<and>
      lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<and>
      lpp_stable_context_holds operation SP incoming_context theta"
      using rho ground preserved by (auto simp: lp_cut_knowledge_def)
  qed
qed

ML \<open>
val checked = [@{thm lpp_finite_local_preserved_split_checked_lower}, @{thm lpp_finite_local_integer_split_checked_lower},
  @{thm lpp_finite_local_ground_split_checked_lower},
  @{thm lpp_finite_local_shape_split_checked_lower}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable guarded return dependency" else ();
\<close>
end
