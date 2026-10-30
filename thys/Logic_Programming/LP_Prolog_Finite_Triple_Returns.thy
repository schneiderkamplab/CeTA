theory LP_Prolog_Finite_Triple_Returns
 imports LP_Prolog_Finite_Triple_Split_Interface LP_Prolog_Finite_Integer_Receipt LP_Prolog_Finite_Ground_Receipt LP_Prolog_Finite_Shape_Receipt
begin
hide_const (open) Tree_Automata_Containment.entry

definition lpp_finite_triple_check_integer_split where
  "lpp_finite_triple_check_integer_split T first_types second_types fuel P D Q roots contexts incoming_context entry receipt evidence =
    (lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts incoming_context
       (lpp_context_add_integers incoming_context (lppsir_integers evidence)) entry receipt \<and>
     lpp_finite_integer_receipt_check P incoming_context (lpcts_pre receipt)
       (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt) (lpcn_vars (lpctr_node entry)) evidence)"

theorem lpp_finite_triple_integer_split_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_finite_triple_check_integer_split T first_types second_types fuel P D Q roots contexts incoming_context entry receipt evidence"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming_context eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      lpp_finite_triple_root_rep SP contexts roots us b ret \<Longrightarrow> lpp_finite_triple_answer_contract P us Q ret"
  shows "lpp_finite_triple_answer_contract P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof -
  have interface: "lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts incoming_context
    (lpp_context_add_integers incoming_context (lppsir_integers evidence)) entry receipt"
    and returns: "lpp_finite_integer_receipt_check P incoming_context (lpcts_pre receipt)
      (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt) (lpcn_vars (lpctr_node entry)) evidence"
    using checked by (auto simp: lpp_finite_triple_check_integer_split_def)
  show ?thesis by (rule lpp_finite_triple_split_interface_lower[OF transfer interface program known observed free
    lpp_finite_integer_receipt_return[OF returns known observed] lower])
qed

definition lpp_finite_triple_check_ground_split where
  "lpp_finite_triple_check_ground_split T first_types second_types fuel P D Q roots contexts incoming_context entry receipt evidence =
    (lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts incoming_context
       (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) entry receipt \<and>
     lpp_finite_ground_receipt_check P incoming_context (lpcts_pre receipt)
       (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt) (lpcn_vars (lpctr_node entry)) evidence)"

theorem lpp_finite_triple_ground_split_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_finite_triple_check_ground_split T first_types second_types fuel P D Q roots contexts incoming_context entry receipt evidence"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming_context eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      lpp_finite_triple_root_rep SP contexts roots us b ret \<Longrightarrow> lpp_finite_triple_answer_contract P us Q ret"
  shows "lpp_finite_triple_answer_contract P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof -
  have interface: "lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts incoming_context
    (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) entry receipt"
    and returns: "lpp_finite_ground_receipt_check P incoming_context (lpcts_pre receipt)
      (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt) (lpcn_vars (lpctr_node entry)) evidence"
    using checked by (auto simp: lpp_finite_triple_check_ground_split_def)
  show ?thesis by (rule lpp_finite_triple_split_interface_lower[OF transfer interface program known observed free
    lpp_finite_ground_receipt_return[OF returns known observed] lower])
qed


definition lpp_finite_triple_check_shape_split where
  "lpp_finite_triple_check_shape_split T first_types second_types fuel P D Q roots contexts incoming_context entry receipt evidence =
    (lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts incoming_context
       (lpp_shape_receipt_context incoming_context evidence) entry receipt \<and>
     lpp_finite_shape_receipt_check P incoming_context (lpcts_pre receipt)
       (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt) (lpcn_vars (lpctr_node entry)) evidence)"

theorem lpp_finite_triple_shape_split_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_finite_triple_check_shape_split T first_types second_types fuel P D Q roots contexts incoming_context entry receipt evidence"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming_context eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      lpp_finite_triple_root_rep SP contexts roots us b ret \<Longrightarrow> lpp_finite_triple_answer_contract P us Q ret"
  shows "lpp_finite_triple_answer_contract P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof -
  have interface: "lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts incoming_context
    (lpp_shape_receipt_context incoming_context evidence) entry receipt"
    and returns: "lpp_finite_shape_receipt_check P incoming_context (lpcts_pre receipt)
      (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt) (lpcn_vars (lpctr_node entry)) evidence"
    using checked by (auto simp: lpp_finite_triple_check_shape_split_def)
  show ?thesis by (rule lpp_finite_triple_split_interface_lower[OF transfer interface program known observed free
    lpp_finite_shape_receipt_return[OF returns known observed] lower])
qed


definition lpp_finite_triple_check_preserved_split where
  "lpp_finite_triple_check_preserved_split T first_types second_types fuel D Q roots contexts incoming_context entry receipt =
    (lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts
      incoming_context incoming_context entry receipt \<and>
     set (lpcts_ground receipt) \<subseteq> set (lpcn_ground (lpctr_node entry)))"

theorem lpp_finite_triple_preserved_split_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_finite_triple_check_preserved_split T first_types second_types fuel D Q roots contexts incoming_context entry receipt"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming_context eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      lpp_finite_triple_root_rep SP contexts roots us b ret \<Longrightarrow> lpp_finite_triple_answer_contract P us Q ret"
  shows "lpp_finite_triple_answer_contract P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof -
  have interface: "lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts
      incoming_context incoming_context entry receipt"
    and subset: "set (lpcts_ground receipt) \<subseteq> set (lpcn_ground (lpctr_node entry))"
    using checked by (auto simp: lpp_finite_triple_check_preserved_split_def)
  show ?thesis
  proof (rule lpp_finite_triple_split_interface_lower[OF transfer interface program known observed free _ lower])
    fix rho
    assume actual: "lpp_finite_actual_return P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho"
    obtain theta where source: "lpp_finite_actual_return P
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) (LPCGoals (lpcts_pre receipt)),eta)] theta"
      and rho: "rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta"
      using lpp_finite_seg_observed_actual[OF actual] by blast
    have preserved: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming_context theta"
      by (rule lpp_finite_actual_return_preserves_context[OF source]) (use observed in simp)
    have ground: "lp_seg_ground (theta x)" if x: "x\<in>set (lpcts_ground receipt)" for x
    proof -
      have finite: "lp_seg_ground (eta x)" using known subset x by (auto simp: lp_cut_knowledge_def)
      have "theta x=eta x"
        using lpp_actual_return_preserves_finite_value[OF finite source, of x] by simp
      then show ?thesis using finite by simp
    qed
    show "\<exists>theta. rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<and>
      lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<and>
      lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming_context theta"
      using rho ground preserved by (auto simp: lp_cut_knowledge_def)
  qed
qed

end
