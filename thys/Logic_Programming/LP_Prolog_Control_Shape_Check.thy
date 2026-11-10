theory LP_Prolog_Control_Shape_Check
 imports LP_Prolog_Control_Shape_Split LP_Prolog_Stable_Guarded_Split_Descent
begin
hide_const (open) Tree_Automata_Containment.entry

definition lpp_check_control_shape_split where
  "lpp_check_control_shape_split T first_types second_types fuel P SP D Q roots contexts
      incoming entry receipt evidence atom OD first_call second_call =
    (lpcts_pre receipt=[LPCAtom (Fun (LPCUser (fst atom)) (snd atom))] \<and>
     lppsir_program (lppsgr_model (lppssr_ground evidence))=SP \<and>
     lpp_control_shape_receipt_check P incoming (lpcts_pre receipt)
       (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt) (lpcn_vars (lpctr_node entry)) evidence \<and>
     lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts incoming
       (lpp_control_shape_context incoming evidence atom) entry receipt \<and>
     lpp_check_finite_guarded_split_descent OD incoming
       (lpp_control_shape_context incoming evidence atom)
       entry receipt first_call second_call)"

theorem lpp_checked_control_shape_split_sound:
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
      lpp_stable_triple_root_rep operation SP contexts roots us b ret \<Longrightarrow> lpp_stable_triple_answer_contract operation P us Q ret"
  shows "lpp_stable_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
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
    by (rule lpp_control_guarded_shape_split_checked_lower[OF compatible transfer
      ground_checked identity pre interface program known observed free first _ lower])
      (use lpp_stable_guarded_split_return_descent[OF descent] in blast)
qed

ML \<open>
val checked = [@{thm lpp_checked_control_shape_split_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable relational Split checker" else ();
\<close>
end
