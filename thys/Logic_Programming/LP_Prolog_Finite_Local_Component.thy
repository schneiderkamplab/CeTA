theory LP_Prolog_Finite_Local_Component
 imports LP_Prolog_Finite_Local_Graph_Check
begin
hide_const (open) Tree_Automata_Containment.entry

theorem lpp_finite_local_component_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_finite_local_component A fuel P D Q T roots contexts incoming entry component"
    and descent: "lpp_check_finite_component_descent OD roots incoming entry component evidence"
    and program: "lp_cut_source_program P"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and observed: "lpp_stable_context_holds operation SP incoming eta"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and finite: "lpp_finite_direct_invariant A (lpc_return_eval eta (lpc_triple_root_state entry))"
    and signature: "\<And>f n. (f,n)\<in>A \<Longrightarrow> (f,n)\<in>lpp_builtin_signature \<Longrightarrow> lpp_direct_arithmetic_name f"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>
        inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP contexts roots us b ret \<Longrightarrow> lpp_finite_direct_invariant A us \<Longrightarrow> lpp_stable_triple_answer_contract operation P us Q ret"
  shows "lpp_stable_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof (cases component)
  case (LPPFTRegion region)
  obtain connections where shape: "evidence=LPPFGRegion connections"
    using descent by (cases evidence) (auto simp: LPPFTRegion)
  have local: "lpp_check_finite_local_region A fuel P D Q T roots contexts incoming entry region (lppftr_contexts region)"
    and guarded: "lpp_check_finite_guarded_region_descent OD roots entry region connections"
    using checked descent by (simp_all add: LPPFTRegion shape)
  show ?thesis by (rule lpp_finite_local_region_descent_checked_lower[OF compatible local guarded program transfer observed known free finite signature lower])
next
  case (LPPFTSplit ft st receipt)
  obtain first_call second_call where shape: "evidence=LPPFGSplit first_call second_call"
    using descent by (cases evidence) (auto simp: LPPFTSplit)
  have local: "lpp_finite_triple_check_preserved_split T ft st fuel D Q roots contexts incoming entry receipt"
    and continuation: "lpp_check_finite_return_goals A (lpcts_ground receipt @
      filter (\<lambda>x. x\<in>lpp_source_context_ground incoming) (lpcn_vars (lpctr_node entry))) (lpcts_rest receipt)"
    and guarded: "lpp_check_finite_guarded_split_descent OD incoming (incoming) entry receipt first_call second_call"
    using checked descent by (auto simp: LPPFTSplit shape)
  have first: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)\<in>
      inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom"
    by (rule lpp_stable_guarded_split_first_descent[OF guarded observed])
  show ?thesis by (rule lpp_finite_local_preserved_split_checked_lower[OF compatible transfer local program known observed free finite continuation first _ lower])
    (use lpp_stable_guarded_split_return_descent[OF guarded] in blast)
next
  case (LPPFTIntegerSplit ft st receipt return_evidence)
  obtain first_call second_call where shape: "evidence=LPPFGSplit first_call second_call"
    using descent by (cases evidence) (auto simp: LPPFTIntegerSplit)
  have local: "lpp_finite_triple_check_integer_split T ft st fuel P D Q roots contexts incoming entry receipt return_evidence"
    and continuation: "lpp_check_finite_return_goals A (lpcts_ground receipt @
      filter (\<lambda>x. x\<in>lpp_source_context_ground (lpp_context_add_integers incoming (lppsir_integers return_evidence))) (lpcn_vars (lpctr_node entry))) (lpcts_rest receipt)"
    and guarded: "lpp_check_finite_guarded_split_descent OD incoming (lpp_context_add_integers incoming (lppsir_integers return_evidence)) entry receipt first_call second_call"
    using checked descent by (auto simp: LPPFTIntegerSplit shape)
  have first: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)\<in>
      inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom"
    by (rule lpp_stable_guarded_split_first_descent[OF guarded observed])
  show ?thesis by (rule lpp_finite_local_integer_split_checked_lower[OF compatible transfer local program known observed free finite continuation first _ lower])
    (use lpp_stable_guarded_split_return_descent[OF guarded] in blast)
next
  case (LPPFTGroundSplit ft st receipt return_evidence)
  obtain first_call second_call where shape: "evidence=LPPFGSplit first_call second_call"
    using descent by (cases evidence) (auto simp: LPPFTGroundSplit)
  have local: "lpp_finite_triple_check_ground_split T ft st fuel P D Q roots contexts incoming entry receipt return_evidence"
    and continuation: "lpp_check_finite_return_goals A (lpcts_ground receipt @
      filter (\<lambda>x. x\<in>lpp_source_context_ground (lpp_context_add_ground incoming (lppsgr_ground return_evidence))) (lpcn_vars (lpctr_node entry))) (lpcts_rest receipt)"
    and guarded: "lpp_check_finite_guarded_split_descent OD incoming (lpp_context_add_ground incoming (lppsgr_ground return_evidence)) entry receipt first_call second_call"
    using checked descent by (auto simp: LPPFTGroundSplit shape)
  have first: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)\<in>
      inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom"
    by (rule lpp_stable_guarded_split_first_descent[OF guarded observed])
  show ?thesis by (rule lpp_finite_local_ground_split_checked_lower[OF compatible transfer local program known observed free finite continuation first _ lower])
    (use lpp_stable_guarded_split_return_descent[OF guarded] in blast)
next
  case (LPPFTShapeSplit ft st receipt return_evidence)
  obtain first_call second_call where shape: "evidence=LPPFGSplit first_call second_call"
    using descent by (cases evidence) (auto simp: LPPFTShapeSplit)
  have local: "lpp_finite_triple_check_shape_split T ft st fuel P D Q roots contexts incoming entry receipt return_evidence"
    and continuation: "lpp_check_finite_return_goals A (lpcts_ground receipt @
      filter (\<lambda>x. x\<in>lpp_source_context_ground (lpp_shape_receipt_context incoming return_evidence)) (lpcn_vars (lpctr_node entry))) (lpcts_rest receipt)"
    and guarded: "lpp_check_finite_guarded_split_descent OD incoming (lpp_shape_receipt_context incoming return_evidence) entry receipt first_call second_call"
    using checked descent by (auto simp: LPPFTShapeSplit shape)
  have first: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)\<in>
      inv_image (lpp_stable_observed_calls operation (set OD) SP) lpp_unlift_atom"
    by (rule lpp_stable_guarded_split_first_descent[OF guarded observed])
  show ?thesis by (rule lpp_finite_local_shape_split_checked_lower[OF compatible transfer local program known observed free finite continuation first _ lower])
    (use lpp_stable_guarded_split_return_descent[OF guarded] in blast)
qed

ML \<open>
val checked = [@{thm lpp_finite_local_component_checked_lower}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite local component" else ();
\<close>
end
