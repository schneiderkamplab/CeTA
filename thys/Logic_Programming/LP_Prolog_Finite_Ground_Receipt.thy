theory LP_Prolog_Finite_Ground_Receipt
 imports LP_Prolog_Finite_Actual_Contexts LP_Prolog_Triple_Ground_Return
begin

fun lpp_finite_ground_prefix_check where
  "lpp_finite_ground_prefix_check F modes G K [LPCAtom (Fun (LPCUser f) ts)] =
    (f\<in>F \<and> f\<noteq>''2:is'' \<and> f\<noteq>''1:integer'' \<and> set K \<subseteq> lp_ground_flow modes [(LPCUser f,ts)] G)"
| "lpp_finite_ground_prefix_check F modes G K _ = False"

definition lpp_finite_ground_receipt_check where
  "lpp_finite_ground_receipt_check P incoming_context pre G H vs evidence =
    (let model=lppsgr_model evidence; K=lppsgr_ground evidence in
     set K \<subseteq> set vs \<and> set H \<subseteq> set G \<union> set K \<and>
     lpp_inline_return_program_check P (set (lppsir_predicates model)) (lppsir_program model) \<and>
     lpp_inline_builtin_check (set (lppsir_predicates model)) (lppsir_program model) \<and>
     lpp_check_transfer_contract (lppsir_summaries model) (lppsir_program model) (lppsir_proofs model) \<and>
     lpp_guarded_ground_check (lppsir_program model) (lppsgr_modes evidence) \<and>
     lpp_finite_ground_prefix_check (set (lppsir_predicates model)) (lppsgr_modes evidence)
       (set G \<union> lpp_source_context_ground incoming_context) K pre)"

lemma lpp_finite_ground_receipt_return:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpp_finite_ground_receipt_check P incoming_context pre G H vs evidence"
    and known: "lp_cut_knowledge (set G) guards eta"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming_context eta"
    and actual: "lpp_finite_actual_return P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
  shows "\<exists>theta. rho=lpc_return_env (map Var vs) theta \<and>
    lp_cut_knowledge (set H) [] theta \<and>
    lpp_evaluation_context_holds lpp_finite_evaluation_result SP (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) theta"
proof -
  let ?model = "lppsgr_model evidence"
  let ?F = "set (lppsir_predicates ?model)"
  let ?SP = "lppsir_program ?model"
  let ?modes = "lppsgr_modes evidence"
  let ?K = "lppsgr_ground evidence"
  let ?G = "set G \<union> lpp_source_context_ground incoming_context"
  obtain f ts where pre: "pre=[LPCAtom (Fun (LPCUser f) ts)]"
    and selected: "f\<in>?F"
    and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and flow: "set ?K \<subseteq> lp_ground_flow ?modes [(LPCUser f,ts)] ?G"
    using checked by (auto simp: lpp_finite_ground_receipt_check_def Let_def
      elim!: lpp_finite_ground_prefix_check.elims)
  have program: "lpp_inline_return_program_check P ?F ?SP"
    and builtin: "lpp_inline_builtin_check ?F ?SP"
    and modes: "lpp_guarded_ground_check ?SP ?modes"
    and cover: "set H \<subseteq> set G \<union> set ?K"
    using checked by (auto simp: lpp_finite_ground_receipt_check_def Let_def)
  obtain theta where source: "lpp_finite_actual_return P [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) (LPCGoals pre),eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    using lpp_finite_seg_observed_actual[OF actual] by blast
  have gr: "\<forall>x\<in>?G. lp_seg_ground (eta x)"
    using known lpp_evaluation_context_ground_sound[OF lpp_finite_evaluation_ground observed] by (auto simp: lp_cut_knowledge_def)
  have result: "\<forall>x\<in>lp_ground_flow ?modes [(LPCUser f,ts)] ?G. lp_seg_ground (theta x)"
    by (rule lpp_inline_guarded_ground_return[OF program builtin selected ordinary modes gr])
      (use source in \<open>simp add: pre\<close>)
  have outputs: "\<forall>x\<in>set ?K. lp_seg_ground (theta x)" using result flow by blast
  have preserved: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming_context theta"
    by (rule lpp_finite_actual_return_preserves_context[OF source]) (use observed in simp)
  have next_context: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP (lpp_context_add_ground incoming_context ?K) theta"
    by (rule lpp_evaluation_add_ground_sound[OF preserved outputs])
  have captured: "theta x=eta x" if x: "x\<in>set G" for x
    using lpp_finite_seg_captured_term[OF source, of "Var x"] gr x by simp
  have ground: "lp_cut_knowledge (set H) [] theta"
    using cover outputs captured gr by (auto simp: lp_cut_knowledge_def)
  show ?thesis using rho ground next_context by blast
qed

end
