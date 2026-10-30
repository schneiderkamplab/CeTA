theory LP_Prolog_Return_Shape_Region
  imports LP_Prolog_Return_Shape_Control LP_Prolog_Finite_Triple_Region
begin

hide_const (open) NthRoot.root Term.root

definition lpp_finite_triple_check_shape_region where
  "lpp_finite_triple_check_shape_region shape_fuel G modes seedss SP fuel P D Q T roots root_contexts incoming_context root region =
    (lp_return_shape_program_check shape_fuel G modes (lpp_shape_program SP) \<and>
     length seedss=length (lpcsc_nodes (lppftr_control region)) \<and>
     list_all (\<lambda>i. set (seedss!i) \<subseteq>
       set (lpcn_ground (lpcsc_nodes (lppftr_control region)!i)) \<union>
       lpp_source_context_ground (lppftr_contexts region!i)) [0..<length seedss] \<and>
     lpp_finite_triple_check_region_contexts fuel P D Q T roots root_contexts incoming_context root region
       (lpp_shape_local_contexts shape_fuel G modes seedss (lppftr_contexts region)))"

theorem lpp_finite_triple_shape_region_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpp_finite_triple_check_shape_region shape_fuel G modes seedss SP fuel P D Q T roots root_contexts incoming_context root region"
    and program: "lp_cut_source_program P"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming_context eta"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node root))) (lpcn_guards (lpctr_node root)) eta"
    and free: "lpc_free_knowledge (set (lpctr_free root)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input root) eta,b)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      lpp_finite_triple_root_rep SP root_contexts roots us b ret \<Longrightarrow> lpp_finite_triple_answer_contract P us Q ret"
  shows "lpp_finite_triple_answer_contract P (lpc_return_eval eta (lpc_triple_root_state root)) Q
    (lp_atom_eval (lpctr_output root))"
proof -
  let ?data = "lppftr_control region"
  have region: "lpp_finite_triple_check_region_contexts fuel P D Q T roots root_contexts incoming_context root region
      (lpp_shape_local_contexts shape_fuel G modes seedss (lppftr_contexts region))"
    using checked by (simp add: lpp_finite_triple_check_shape_region_def)
  have control: "lpp_check_shape_evaluation_control shape_fuel G modes seedss SP fuel P (lpcsc_program ?data)
      (lpcsc_nodes ?data) (lpcsc_states ?data) (lppftr_contexts region) (lppftr_free region) T
      (lpcsc_returned ?data) (lpcsc_arity ?data) (lppftr_actions region)"
    using checked by (auto simp: lpp_check_shape_evaluation_control_def
      lpp_finite_triple_check_shape_region_def lpp_finite_triple_check_region_contexts_def Let_def)
  show ?thesis
    by (rule lpp_finite_triple_region_contexts_checked_lower[OF region _ program transfer observed known free lower])
      (rule lpp_check_shape_evaluation_control_enrich[OF control]; assumption)
qed

end
