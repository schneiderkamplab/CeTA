theory LP_Prolog_Finite_Integer_Receipt
 imports LP_Prolog_Finite_Actual_Contexts LP_Prolog_Triple_Ground_Return
begin

fun lpp_finite_integer_prefix_check where
  "lpp_finite_integer_prefix_check F T guards facts K [LPCAtom (Fun (LPCUser f) ts)] =
    (f\<in>F \<and> f\<noteq>''2:is'' \<and> f\<noteq>''1:integer'' \<and> lpp_check_operation_context T [(f,ts)] guards facts K)"
| "lpp_finite_integer_prefix_check F T guards facts K _ = False"

definition lpp_finite_integer_receipt_check where
  "lpp_finite_integer_receipt_check P incoming_context pre G H vs evidence =
    (set (lppsir_integers evidence) \<subseteq> set vs \<and>
     set H \<subseteq> set G \<union> set (lppsir_integers evidence) \<and>
     lpp_inline_return_program_check P (set (lppsir_predicates evidence)) (lppsir_program evidence) \<and>
     lpp_inline_builtin_check (set (lppsir_predicates evidence)) (lppsir_program evidence) \<and>
     lpp_check_transfer_contract (lppsir_summaries evidence) (lppsir_program evidence) (lppsir_proofs evidence) \<and>
     lpp_finite_integer_prefix_check (set (lppsir_predicates evidence))
       (lpp_transfer_lookup (lppsir_summaries evidence)) (fst (snd incoming_context))
       (lppsir_facts evidence) (lppsir_integers evidence) pre)"


lemma lpp_finite_integer_receipt_return:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpp_finite_integer_receipt_check P incoming_context pre G H vs evidence"
    and known: "lp_cut_knowledge (set G) guards eta"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming_context eta"
    and actual: "lpp_finite_actual_return P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
  shows "\<exists>theta. rho=lpc_return_env (map Var vs) theta \<and>
    lp_cut_knowledge (set H) [] theta \<and>
    lpp_evaluation_context_holds lpp_finite_evaluation_result SP (lpp_context_add_integers incoming_context (lppsir_integers evidence)) theta"
proof -
  let ?F = "set (lppsir_predicates evidence)"
  let ?SP = "lppsir_program evidence"
  let ?T = "lpp_transfer_lookup (lppsir_summaries evidence)"
  let ?K = "lppsir_integers evidence"
  obtain f ts where pre: "pre=[LPCAtom (Fun (LPCUser f) ts)]"
    and selected: "f\<in>?F"
    and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and typing: "lpp_check_operation_context ?T [(f,ts)] (fst (snd incoming_context)) (lppsir_facts evidence) ?K"
    using checked by (auto simp: lpp_finite_integer_receipt_check_def Let_def
      elim!: lpp_finite_integer_prefix_check.elims)
  have program: "lpp_inline_return_program_check P ?F ?SP"
    and builtin: "lpp_inline_builtin_check ?F ?SP"
    and transfer: "lpp_check_transfer_program ?T ?SP (lppsir_proofs evidence)"
    and cover: "set H \<subseteq> set G \<union> set ?K"
    using checked by (auto simp: lpp_finite_integer_receipt_check_def Let_def lpp_check_transfer_contract_def)
  obtain theta where source: "lpp_finite_actual_return P [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) (LPCGoals pre),eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    using lpp_finite_seg_observed_actual[OF actual] by blast
  have guards: "list_all (lpp_success_guard_holds lpp_finite_evaluation_result eta) (fst (snd incoming_context))"
    using observed by (cases incoming_context) (simp add: lpp_evaluation_context_holds_def)
  have integers: "lpp_integer_known ?K theta"
    by (rule lpp_inline_finite_integer_return[OF program builtin selected ordinary transfer typing guards])
      (use source in \<open>simp add: pre\<close>)
  have preserved: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming_context theta"
    by (rule lpp_finite_actual_return_preserves_context[OF source]) (use observed in simp)
  have next_context: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP (lpp_context_add_integers incoming_context ?K) theta"
    by (rule lpp_evaluation_add_integers_sound[OF preserved integers])
  have gr: "\<forall>x\<in>set G. lp_seg_ground (eta x)" using known by (simp add: lp_cut_knowledge_def)
  have captured: "theta x=eta x" if x: "x\<in>set G" for x
    using lpp_finite_seg_captured_term[OF source, of "Var x"] gr x by simp
  have each_ground: "lp_seg_ground (theta x)" if x: "x\<in>set H" for x
  proof (cases "x\<in>set G")
    case True
    show ?thesis using gr captured[OF True] True by simp
  next
    case False
    have member: "x\<in>set ?K" using cover x False by blast
    obtain n where literal: "theta x=lpp_integer_value n"
      using integers member by (auto simp: lpp_integer_known_def)
    show ?thesis by (auto simp: literal lpp_integer_value_def intro: lp_seg_ground.intros)
  qed
  have ground: "lp_cut_knowledge (set H) [] theta"
    using each_ground by (simp add: lp_cut_knowledge_def)
  show ?thesis using rho ground next_context by blast
qed

end
