theory LP_Prolog_Open_Relational_Split
 imports LP_Prolog_Control_Relational_Split
begin
hide_const (open) Tree_Automata_Containment.entry

theorem lpp_open_guarded_relational_ground_split_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and ground_checked: "lpp_open_ground_receipt_check P incoming_context
      (lpcts_pre receipt) (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt)
      (lpcn_vars (lpctr_node entry)) evidence"
    and model_identity: "lppsir_program (lppsgr_model evidence)=SP"
    and pre: "lpcts_pre receipt=[LPCAtom (Fun (LPCUser f) ts)]"
    and checked: "lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts
      incoming_context (lpp_context_add_success (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) (f,ts)) entry receipt"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and first_descent: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)\<in>R"
    and return_descent: "\<And>rho theta. lpp_stable_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho \<Longrightarrow>
      rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<Longrightarrow>
      lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<Longrightarrow>
      lpp_stable_context_holds operation SP (lpp_context_add_success (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) (f,ts)) theta \<Longrightarrow>
      (lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_second_in receipt) theta)\<in>R"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>R \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP contexts roots us b ret \<Longrightarrow> lpp_stable_triple_answer_contract operation P us Q ret"
  shows "lpp_stable_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof -
  show ?thesis
  proof (rule lpp_stable_guarded_split_interface_lower[OF compatible transfer checked program known observed free _ first_descent return_descent lower])
    fix rho
    assume actual: "lpp_stable_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho"
    obtain theta where rho: "rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta"
      and ground: "lp_cut_knowledge (set (lpcts_ground receipt)) [] theta"
      and returned: "lpp_stable_context_holds operation SP
        (lpp_context_add_success (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) (f,ts)) theta"
      using lpp_open_relational_ground_receipt_return[OF compatible ground_checked model_identity pre known observed actual]
      by blast
    show "\<exists>theta. rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<and>
      lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<and>
      lpp_stable_context_holds operation SP (lpp_context_add_success (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) (f,ts)) theta"
      using rho ground returned by blast
  qed
qed

definition lpp_mixed_ground_receipt_check where
  "lpp_mixed_ground_receipt_check P incoming pre G H vs evidence =
    (lpp_finite_ground_receipt_check P incoming pre G H vs evidence \<or>
     lpp_open_ground_receipt_check P incoming pre G H vs evidence \<or>
     lpp_control_ground_receipt_check P incoming pre G H vs evidence)"

theorem lpp_mixed_guarded_relational_ground_split_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and ground_checked: "lpp_mixed_ground_receipt_check P incoming_context
      (lpcts_pre receipt) (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt)
      (lpcn_vars (lpctr_node entry)) evidence"
    and model_identity: "lppsir_program (lppsgr_model evidence)=SP"
    and pre: "lpcts_pre receipt=[LPCAtom (Fun (LPCUser f) ts)]"
    and checked: "lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts
      incoming_context (lpp_context_add_success (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) (f,ts)) entry receipt"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and first_descent: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)\<in>R"
    and return_descent: "\<And>rho theta. lpp_stable_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho \<Longrightarrow>
      rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<Longrightarrow>
      lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<Longrightarrow>
      lpp_stable_context_holds operation SP (lpp_context_add_success (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) (f,ts)) theta \<Longrightarrow>
      (lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_second_in receipt) theta)\<in>R"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>R \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP contexts roots us b ret \<Longrightarrow> lpp_stable_triple_answer_contract operation P us Q ret"
  shows "lpp_stable_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof -
  consider (old) "lpp_finite_ground_receipt_check P incoming_context (lpcts_pre receipt)
      (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt) (lpcn_vars (lpctr_node entry)) evidence"
    | (legacy_open) "lpp_open_ground_receipt_check P incoming_context (lpcts_pre receipt)
      (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt) (lpcn_vars (lpctr_node entry)) evidence"
    | (control) "lpp_control_ground_receipt_check P incoming_context (lpcts_pre receipt)
      (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt) (lpcn_vars (lpctr_node entry)) evidence"
    using ground_checked by (auto simp: lpp_mixed_ground_receipt_check_def)
  then show ?thesis
  proof cases
    case old
    show ?thesis by (rule lpp_stable_guarded_relational_ground_split_checked_lower[OF compatible transfer old
      model_identity pre checked program known observed free first_descent return_descent lower])
  next
    case legacy_open
    show ?thesis by (rule lpp_open_guarded_relational_ground_split_checked_lower[OF compatible transfer legacy_open
      model_identity pre checked program known observed free first_descent return_descent lower])
  next
    case control
    show ?thesis by (rule lpp_control_guarded_relational_ground_split_checked_lower[OF compatible transfer control
      model_identity pre checked program known observed free first_descent return_descent lower])
  qed
qed

ML \<open>
val checked = [@{thm lpp_mixed_guarded_relational_ground_split_checked_lower}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted mixed relational Split" else ();
\<close>
end
