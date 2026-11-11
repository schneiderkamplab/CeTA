theory LP_Prolog_Stopped_Relational_Check
 imports LP_Prolog_Stopped_Guarded_Split LP_Prolog_Stable_Relational_Check LP_Prolog_Control_Shape_Check
begin
hide_const (open) Tree_Automata_Containment.entry

lemma lpp_stopped_mixed_ground_receipt_return:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_mixed_ground_receipt_check P incoming_context pre G H vs evidence"
    and model_identity: "lppsir_program (lppsgr_model evidence)=SP"
    and prefix: "pre=[LPCAtom (Fun (LPCUser f) ts)]"
    and known: "lp_cut_knowledge (set G) guards eta"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and actual: "lpp_stopped_actual_return operation P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
  shows "\<exists>theta. rho=lpc_return_env (map Var vs) theta \<and>
    lp_cut_knowledge (set H) [] theta \<and>
    lpp_stable_context_holds operation SP (lpp_context_add_success (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) (f,ts)) theta"
proof -
  have ordinary: "lpp_stable_actual_return operation P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
    by (rule lp_answer_stop_actual[OF actual])
  show ?thesis using checked
    lpp_stable_relational_ground_receipt_return[OF compatible _ model_identity prefix known observed ordinary]
    lpp_open_relational_ground_receipt_return[OF compatible _ model_identity prefix known observed ordinary]
    lpp_control_relational_ground_receipt_return[OF compatible _ model_identity prefix known observed ordinary]
    by (auto simp: lpp_mixed_ground_receipt_check_def)
qed

theorem lpp_checked_stopped_relational_split_sound:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_stable_relational_split T first_types second_types fuel P SP D Q roots contexts
      incoming_context entry receipt evidence (f,ts) OD first_call second_call"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP contexts roots us b ret \<Longrightarrow> lpp_stopped_triple_answer_contract operation P us Q ret"
  shows "lpp_stopped_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof -
  have ground_checked: "lpp_mixed_ground_receipt_check P incoming_context
      (lpcts_pre receipt) (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt)
      (lpcn_vars (lpctr_node entry)) evidence"
    and identity: "lppsir_program (lppsgr_model evidence)=SP"
    and pre: "lpcts_pre receipt=[LPCAtom (Fun (LPCUser f) ts)]"
    and interface: "lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts
      incoming_context (lpp_context_add_success (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) (f,ts)) entry receipt"
    and descent: "lpp_check_finite_guarded_split_descent OD incoming_context
      (lpp_context_add_success (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) (f,ts))
      entry receipt first_call second_call"
    using checked by (auto simp: lpp_check_stable_relational_split_def)
  have first: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)
      \<in>inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom"
    by (rule lpp_stable_guarded_split_first_descent[OF descent observed])
  show ?thesis
  proof (rule lpp_stopped_guarded_split_interface_lower[OF compatible transfer interface program known observed free _ first _ lower])
    fix rho
    assume actual: "lpp_stopped_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho"
    show "\<exists>theta. rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<and>
      lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<and>
      lpp_stable_context_holds operation SP (lpp_context_add_success (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) (f,ts)) theta"
      by (rule lpp_stopped_mixed_ground_receipt_return[OF compatible ground_checked identity pre known observed actual])
  next
    fix rho theta
    assume actual: "lpp_stopped_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho"
      and returned: "rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta"
      and ground: "lp_cut_knowledge (set (lpcts_ground receipt)) [] theta"
      and facts: "lpp_stable_context_holds operation SP (lpp_context_add_success (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) (f,ts)) theta"
    show "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_second_in receipt) theta)
      \<in>inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom"
      by (rule lpp_stable_guarded_split_return_descent[OF descent lp_answer_stop_actual[OF actual] returned facts])
  qed
qed

theorem lpp_checked_stopped_shape_split_sound:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and checked: "lpp_check_control_shape_split T first_types second_types fuel P SP D Q roots contexts
      incoming_context entry receipt evidence (f,ts) OD first_call second_call"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP contexts roots us b ret \<Longrightarrow> lpp_stopped_triple_answer_contract operation P us Q ret"
  shows "lpp_stopped_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof -
  have ground_checked: "lpp_control_shape_receipt_check P incoming_context
      (lpcts_pre receipt) (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt)
      (lpcn_vars (lpctr_node entry)) evidence"
    and identity: "lppsir_program (lppsgr_model (lppssr_ground evidence))=SP"
    and pre: "lpcts_pre receipt=[LPCAtom (Fun (LPCUser f) ts)]"
    and interface: "lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts
      incoming_context (lpp_control_shape_context incoming_context evidence (f,ts)) entry receipt"
    and descent: "lpp_check_finite_guarded_split_descent OD incoming_context
      (lpp_control_shape_context incoming_context evidence (f,ts))
      entry receipt first_call second_call"
    using checked by (auto simp: lpp_check_control_shape_split_def)
  have first: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)
      \<in>inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom"
    by (rule lpp_stable_guarded_split_first_descent[OF descent observed])
  show ?thesis
  proof (rule lpp_stopped_guarded_split_interface_lower[OF compatible transfer interface program known observed free _ first _ lower])
    fix rho
    assume actual: "lpp_stopped_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho"
    show "\<exists>theta. rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<and>
      lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<and>
      lpp_stable_context_holds operation SP (lpp_control_shape_context incoming_context evidence (f,ts)) theta"
      by (rule lpp_control_shape_receipt_return[OF compatible ground_checked identity pre known observed lp_answer_stop_actual[OF actual]])
  next
    fix rho theta
    assume actual: "lpp_stopped_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho"
      and returned: "rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta"
      and ground: "lp_cut_knowledge (set (lpcts_ground receipt)) [] theta"
      and facts: "lpp_stable_context_holds operation SP (lpp_control_shape_context incoming_context evidence (f,ts)) theta"
    show "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_second_in receipt) theta)
      \<in>inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom"
      by (rule lpp_stable_guarded_split_return_descent[OF descent lp_answer_stop_actual[OF actual] returned facts])
  qed
qed

ML \<open>
val checked = [@{thm lpp_checked_stopped_relational_split_sound}, @{thm lpp_checked_stopped_shape_split_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stopped relational Split dependency" else ();
\<close>
end
