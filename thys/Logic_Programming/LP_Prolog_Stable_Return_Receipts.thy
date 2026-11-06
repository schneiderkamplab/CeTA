theory LP_Prolog_Stable_Return_Receipts
 imports LP_Prolog_Stable_Preserved_Split LP_Prolog_Finite_Integer_Receipt LP_Prolog_Finite_Ground_Receipt
begin

lemma lp_actual_answer_transition_refinement:
  assumes refines: "\<And>xs ev ys. U xs ev ys \<Longrightarrow> T xs ev ys"
    and actual: "lp_actual_answer U ss eta"
  shows "lp_actual_answer T ss eta"
proof -
  have included: "lp_answer_steps U \<subseteq> lp_answer_steps T"
    using refines by (auto simp: lp_answer_steps_def)
  have paths: "(lp_answer_steps U)\<^sup>* \<subseteq> (lp_answer_steps T)\<^sup>*"
    by (rule rtrancl_mono[OF included])
  obtain us vs where path: "(ss,us)\<in>(lp_answer_steps U)\<^sup>*"
    and event: "U us (Some eta) vs" using actual by (auto simp: lp_actual_answer_def)
  have old_path: "(ss,us)\<in>(lp_answer_steps T)\<^sup>*" by (rule subsetD[OF paths path])
  have old_event: "T us (Some eta) vs" by (rule refines[OF event])
  show ?thesis using old_path old_event by (auto simp: lp_actual_answer_def)
qed

lemma lpp_stable_actual_return_finite:
  "lpp_stable_actual_return operation P ss eta \<Longrightarrow> lpp_finite_actual_return P ss eta"
  by (rule lp_actual_answer_transition_refinement[OF lpp_stable_domain_answers_refine]) assumption

lemma lpp_stable_add_integers_sound:
  "lpp_stable_context_holds operation SP incoming eta \<Longrightarrow>
   lpp_integer_known K eta \<Longrightarrow>
    lpp_stable_context_holds operation SP (lpp_context_add_integers incoming K) eta"
  by (cases incoming) (auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def
    lpp_integer_known_def lpp_is_integer_def list_all_iff)

lemma lpp_stable_integer_receipt_return:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_finite_integer_receipt_check P incoming_context pre G H vs evidence"
    and known: "lp_cut_knowledge (set G) guards eta"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and actual: "lpp_stable_actual_return operation P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
  shows "\<exists>theta. rho=lpc_return_env (map Var vs) theta \<and>
    lp_cut_knowledge (set H) [] theta \<and>
    lpp_stable_context_holds operation SP (lpp_context_add_integers incoming_context (lppsir_integers evidence)) theta"
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
  obtain theta where source: "lpp_stable_actual_return operation P [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) (LPCGoals pre),eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    using lpp_stable_seg_observed_actual[OF actual] by blast
  have guards: "list_all (lpp_success_guard_holds lpp_finite_evaluation_result eta) (fst (snd incoming_context))"
    using lpp_stable_context_finite_envelope[OF compatible observed] by (cases incoming_context) (simp add: lpp_evaluation_context_holds_def)
  have integers: "lpp_integer_known ?K theta"
    by (rule lpp_inline_finite_integer_return[OF program builtin selected ordinary transfer typing guards])
      (use lpp_stable_actual_return_finite[OF source] in \<open>simp add: pre\<close>)
  have preserved: "lpp_stable_context_holds operation SP incoming_context theta"
    by (rule lpp_stable_actual_return_preserves_context[OF source]) (use observed in simp)
  have next_context: "lpp_stable_context_holds operation SP (lpp_context_add_integers incoming_context ?K) theta"
    by (rule lpp_stable_add_integers_sound[OF preserved integers])
  have gr: "\<forall>x\<in>set G. lp_seg_ground (eta x)" using known by (simp add: lp_cut_knowledge_def)
  have captured: "theta x=eta x" if x: "x\<in>set G" for x
    using lpp_stable_seg_captured_term[OF source, of "Var x"] gr x by simp
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


lemma lpp_stable_ground_receipt_return:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_finite_ground_receipt_check P incoming_context pre G H vs evidence"
    and known: "lp_cut_knowledge (set G) guards eta"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and actual: "lpp_stable_actual_return operation P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
  shows "\<exists>theta. rho=lpc_return_env (map Var vs) theta \<and>
    lp_cut_knowledge (set H) [] theta \<and>
    lpp_stable_context_holds operation SP (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) theta"
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
  obtain theta where source: "lpp_stable_actual_return operation P [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) (LPCGoals pre),eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    using lpp_stable_seg_observed_actual[OF actual] by blast
  have gr: "\<forall>x\<in>?G. lp_seg_ground (eta x)"
    using known lpp_evaluation_context_ground_sound[OF lpp_finite_evaluation_ground lpp_stable_context_finite_envelope[OF compatible observed]] by (auto simp: lp_cut_knowledge_def)
  have result: "\<forall>x\<in>lp_ground_flow ?modes [(LPCUser f,ts)] ?G. lp_seg_ground (theta x)"
    by (rule lpp_inline_guarded_ground_return[OF program builtin selected ordinary modes gr])
      (use lpp_stable_actual_return_finite[OF source] in \<open>simp add: pre\<close>)
  have outputs: "\<forall>x\<in>set ?K. lp_seg_ground (theta x)" using result flow by blast
  have preserved: "lpp_stable_context_holds operation SP incoming_context theta"
    by (rule lpp_stable_actual_return_preserves_context[OF source]) (use observed in simp)
  have next_context: "lpp_stable_context_holds operation SP (lpp_context_add_ground incoming_context ?K) theta"
    by (rule lpp_stable_add_ground_sound[OF preserved outputs])
  have captured: "theta x=eta x" if x: "x\<in>set G" for x
    using lpp_stable_seg_captured_term[OF source, of "Var x"] gr x by simp
  have ground: "lp_cut_knowledge (set H) [] theta"
    using cover outputs captured gr by (auto simp: lp_cut_knowledge_def)
  show ?thesis using rho ground next_context by blast
qed


ML \<open>
val checked = [@{thm lp_actual_answer_transition_refinement}, @{thm lpp_stable_actual_return_finite},
  @{thm lpp_stable_add_integers_sound}, @{thm lpp_stable_integer_receipt_return},
  @{thm lpp_stable_ground_receipt_return}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable return receipt dependency" else ();
\<close>
end
