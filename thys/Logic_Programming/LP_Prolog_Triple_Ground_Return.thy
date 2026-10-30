theory LP_Prolog_Triple_Ground_Return
 imports LP_Prolog_Triple_Integer_Return LP_Prolog_Source_Ground_Return
begin

hide_const (open) Tree_Automata_Containment.entry

record lpp_source_ground_receipt =
  lppsgr_model :: lpp_source_integer_receipt
  lppsgr_modes :: "string lp_cut_symbol lp_ground_mode list"
  lppsgr_ground :: "string list"

fun lpp_source_ground_prefix_check where
  "lpp_source_ground_prefix_check F modes G K [LPCAtom (Fun (LPCUser f) ts)] =
    (f\<in>F \<and> set K \<subseteq> lp_ground_flow modes [(LPCUser f,ts)] G)"
| "lpp_source_ground_prefix_check F modes G K _ = False"

definition lpp_source_ground_receipt_check where
  "lpp_source_ground_receipt_check P incoming_context pre G H vs evidence =
    (let model=lppsgr_model evidence; K=lppsgr_ground evidence in
     set K \<subseteq> set vs \<and> set H \<subseteq> set G \<union> set K \<and>
     lpp_source_return_program_check P (set (lppsir_predicates model)) (lppsir_program model) \<and>
     lpp_return_builtin_check (set (lppsir_predicates model)) (lppsir_program model) \<and>
     lpp_check_transfer_contract (lppsir_summaries model) (lppsir_program model) (lppsir_proofs model) \<and>
     lp_ground_check (lpp_erase_success (lppsir_program model)) (lppsgr_modes evidence) \<and>
     lpp_source_ground_prefix_check (set (lppsir_predicates model)) (lppsgr_modes evidence)
       (set G \<union> lpp_source_context_ground incoming_context) K pre)"

lemma lpp_source_ground_receipt_return:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpp_source_ground_receipt_check P incoming_context pre G H vs evidence"
    and known: "lp_cut_knowledge (set G) guards eta"
    and observed: "lpp_source_context_holds SP incoming_context eta"
    and actual: "lpp_actual_return P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
  shows "\<exists>theta. rho=lpc_return_env (map Var vs) theta \<and>
    lp_cut_knowledge (set H) [] theta \<and>
    lpp_source_context_holds SP (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) theta"
proof -
  let ?model = "lppsgr_model evidence"
  let ?F = "set (lppsir_predicates ?model)"
  let ?SP = "lppsir_program ?model"
  let ?modes = "lppsgr_modes evidence"
  let ?K = "lppsgr_ground evidence"
  let ?G = "set G \<union> lpp_source_context_ground incoming_context"
  obtain f ts where pre: "pre=[LPCAtom (Fun (LPCUser f) ts)]"
    and selected: "f\<in>?F"
    and flow: "set ?K \<subseteq> lp_ground_flow ?modes [(LPCUser f,ts)] ?G"
    using checked by (auto simp: lpp_source_ground_receipt_check_def Let_def
      elim!: lpp_source_ground_prefix_check.elims)
  have program: "lpp_source_return_program_check P ?F ?SP"
    and builtin: "lpp_return_builtin_check ?F ?SP"
    and modes: "lp_ground_check (lpp_erase_success ?SP) ?modes"
    and cover: "set H \<subseteq> set G \<union> set ?K"
    using checked by (auto simp: lpp_source_ground_receipt_check_def Let_def)
  obtain theta where source: "lpp_actual_return P [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) (LPCGoals pre),eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    using lpp_seg_observed_actual[OF actual] by blast
  have gr: "\<forall>x\<in>?G. lp_seg_ground (eta x)"
    using known lpp_source_context_ground_sound[OF observed] by (auto simp: lp_cut_knowledge_def)
  have result: "\<forall>x\<in>lp_ground_flow ?modes [(LPCUser f,ts)] ?G. lp_seg_ground (theta x)"
    by (rule lpp_source_ground_return[OF program builtin selected modes gr])
      (use source in \<open>simp add: pre\<close>)
  have outputs: "\<forall>x\<in>set ?K. lp_seg_ground (theta x)" using result flow by blast
  have preserved: "lpp_source_context_holds SP incoming_context theta"
    by (rule lpp_actual_return_preserves_context[OF source]) (use observed in simp)
  have next_context: "lpp_source_context_holds SP (lpp_context_add_ground incoming_context ?K) theta"
    by (rule lpp_context_add_ground_sound[OF preserved outputs])
  have captured: "theta x=eta x" if x: "x\<in>set G" for x
    using lpp_seg_captured_term[OF source, of "Var x"] gr x by simp
  have ground: "lp_cut_knowledge (set H) [] theta"
    using cover outputs captured gr by (auto simp: lp_cut_knowledge_def)
  show ?thesis using rho ground next_context by blast
qed

definition lpp_triple_check_ground_split where
  "lpp_triple_check_ground_split fuel P D Q roots contexts incoming_context entry receipt evidence =
    (lpp_triple_check_split_interface fuel D Q roots contexts incoming_context
       (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) entry receipt \<and>
     lpp_source_ground_receipt_check P incoming_context (lpcts_pre receipt)
       (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt) (lpcn_vars (lpctr_node entry)) evidence)"

theorem lpp_triple_ground_split_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpp_triple_check_ground_split fuel P D Q roots contexts incoming_context entry receipt evidence"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and observed: "lpp_source_context_holds SP incoming_context eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>lp_triple_calls (set D) Q \<Longrightarrow>
      lpp_triple_root_rep SP contexts roots us b ret \<Longrightarrow> lpp_triple_answer_contract P us Q ret"
  shows "lpp_triple_answer_contract P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof -
  have interface: "lpp_triple_check_split_interface fuel D Q roots contexts incoming_context
    (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) entry receipt"
    and returns: "lpp_source_ground_receipt_check P incoming_context (lpcts_pre receipt)
      (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt) (lpcn_vars (lpctr_node entry)) evidence"
    using checked by (auto simp: lpp_triple_check_ground_split_def)
  show ?thesis by (rule lpp_triple_split_interface_lower[OF interface program known observed free
    lpp_source_ground_receipt_return[OF returns known observed] lower])
qed

end
