theory LP_Prolog_Control_Shape_Receipt
 imports LP_Prolog_Control_Ground_Receipt LP_Prolog_Return_Productivity LP_Prolog_Stable_Shape_Receipt
begin

definition lpp_control_shape_context where
  "lpp_control_shape_context incoming evidence atom =
    lpp_context_add_shapes
      (lpp_context_add_integers (lpp_context_add_success
        (lpp_context_add_ground incoming (lppsgr_ground (lppssr_ground evidence))) atom)
        (lppsir_integers (lppsgr_model (lppssr_ground evidence))))
      (lppssr_grammar evidence) (lppssr_outputs evidence)"

fun lpp_control_integer_prefix_check where
  "lpp_control_integer_prefix_check incoming return_model [LPCAtom (Fun (LPCUser f) ts)] =
    lpp_check_operation_context (lpp_transfer_lookup (lppsir_summaries return_model)) [(f,ts)]
      (fst (snd incoming)) (lppsir_facts return_model) (lppsir_integers return_model)"
| "lpp_control_integer_prefix_check incoming return_model _ = False"

definition lpp_control_shape_receipt_check where
  "lpp_control_shape_receipt_check P incoming pre G H vs evidence =
    (lpp_control_ground_receipt_check P incoming pre G G vs (lppssr_ground evidence) \<and>
     lpp_control_integer_prefix_check incoming (lppsgr_model (lppssr_ground evidence)) pre \<and>
     set H \<subseteq> set G \<union> set (lppsgr_ground (lppssr_ground evidence)) \<union>
       set (lppsir_integers (lppsgr_model (lppssr_ground evidence))) \<union>
       set (map snd (filter (\<lambda>(shape,x). shape=LPReturnGround) (lppssr_outputs evidence))) \<and>
     set (map snd (lppssr_outputs evidence)) \<subseteq> set vs \<and>
     lp_return_nonproductive_check (lpp_shape_program (lppsir_program (lppsgr_model (lppssr_ground evidence))))
       (lppssr_nonproductive evidence) \<and>
     lp_return_shape_program_check (lppssr_fuel evidence) (lppssr_grammar evidence)
       (lppssr_modes evidence) (lp_return_productive_program
         (lpp_shape_program (lppsir_program (lppsgr_model (lppssr_ground evidence)))) (lppssr_nonproductive evidence)) \<and>
     lpp_shape_seed_check (lppssr_grammar evidence) G incoming (lppssr_seeds evidence) \<and>
     lpp_finite_shape_prefix_check (set (lppsir_predicates (lppsgr_model (lppssr_ground evidence))))
       (lppssr_fuel evidence) (lppssr_grammar evidence) (lppssr_modes evidence)
       (lppssr_seeds evidence) (lppssr_outputs evidence) pre)"

lemma lpp_control_shape_receipt_return:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_control_shape_receipt_check P incoming_context pre G H vs evidence"
    and model_identity: "lppsir_program (lppsgr_model (lppssr_ground evidence))=SP"
    and prefix: "pre=[LPCAtom (Fun (LPCUser f) ts)]"
    and known: "lp_cut_knowledge (set G) guards eta"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and actual: "lpp_stable_actual_return operation P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
  shows "\<exists>theta. rho=lpc_return_env (map Var vs) theta \<and>
    lp_cut_knowledge (set H) [] theta \<and>
    lpp_stable_context_holds operation SP (lpp_control_shape_context incoming_context evidence (f,ts)) theta"
proof -
  have base_checked: "lpp_control_ground_receipt_check P incoming_context pre G G vs (lppssr_ground evidence)"
    using checked by (simp add: lpp_control_shape_receipt_check_def)
  let ?model = "lppsgr_model (lppssr_ground evidence)"
  let ?F = "set (lppsir_predicates ?model)"
  let ?SP = "lppsir_program ?model"
  let ?modes = "lppsgr_modes (lppssr_ground evidence)"
  let ?K = "lppsgr_ground (lppssr_ground evidence)"
  let ?G = "set G \<union> lpp_source_context_ground incoming_context"
  have selected: "f\<in>?F"
    and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''" "f\<noteq>''2:;''" "f\<noteq>''3:subtract''"
    and flow: "set ?K \<subseteq> lp_ground_flow ?modes [(LPCUser f,ts)] ?G"
    using base_checked prefix by (auto simp: lpp_control_ground_receipt_check_def Let_def
      elim!: lpp_finite_ground_prefix_check.elims)
  have program: "lpp_control_return_program_check 256 P ?F ?SP"
    and builtin: "lpp_open_builtin_check ?F ?SP"
    and modes: "lpp_guarded_ground_check ?SP ?modes"
    using base_checked by (auto simp: lpp_control_ground_receipt_check_def Let_def)
  obtain theta where source: "lpp_stable_actual_return operation P [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) (LPCGoals pre),eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    using lpp_stable_seg_observed_actual[OF actual] by blast
  have gr: "\<forall>x\<in>?G. lp_seg_ground (eta x)"
    using known lpp_evaluation_context_ground_sound[OF lpp_finite_evaluation_ground lpp_stable_context_finite_envelope[OF compatible observed]] by (auto simp: lp_cut_knowledge_def)
  have source_call: "lpp_stable_actual_return operation P
    [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] theta"
    using source by (simp add: prefix)
  have success: "lpp_guarded_success ?SP (lpp_stable_scalar_evaluation operation)
      (lpp_success_atom_eval (f,ts) theta)"
    by (rule lpp_control_stable_relational_return[where eta=eta, OF program builtin selected ordinary source_call])
  have gr_after: "\<forall>x\<in>?G. lp_seg_ground (theta x)"
    using lpp_stable_seg_captured_term[OF source, of "Var _"] gr by fastforce
  have result: "\<forall>x\<in>lp_ground_flow ?modes [(LPCUser f,ts)] ?G. lp_seg_ground (theta x)"
    by (rule lpp_open_stable_ground_flow[OF compatible modes success gr_after])
  have outputs: "\<forall>x\<in>set ?K. lp_seg_ground (theta x)" using result flow by blast
  have preserved: "lpp_stable_context_holds operation SP incoming_context theta"
    by (rule lpp_stable_actual_return_preserves_context[OF source]) (use observed in simp)
  have next_context: "lpp_stable_context_holds operation SP (lpp_context_add_ground incoming_context ?K) theta"
    by (rule lpp_stable_add_ground_sound[OF preserved outputs])
  have captured: "theta x=eta x" if x: "x\<in>set G" for x
    using lpp_stable_seg_captured_term[OF source, of "Var x"] gr x by simp
  have relation: "lpp_guarded_success SP (lpp_stable_scalar_evaluation operation)
      (lpp_success_atom_eval (f,ts) theta)"
    using success model_identity by simp
  have enriched: "lpp_stable_context_holds operation SP
      (lpp_context_add_success (lpp_context_add_ground incoming_context ?K) (f,ts)) theta"
    by (rule lpp_stable_add_success[OF next_context relation])
  obtain shape_result where shape_flow:
      "lp_return_shape_transfer (lppssr_fuel evidence) (lppssr_grammar evidence)
        (lppssr_modes evidence) (LPCUser f,ts) (Some (lppssr_seeds evidence))=Some shape_result"
    and keep: "set (lppssr_outputs evidence) \<subseteq> set shape_result"
    using checked prefix by (auto simp: lpp_control_shape_receipt_check_def
      elim!: lpp_finite_shape_prefix_check.elims split: option.splits)
  have productive_check: "lp_return_nonproductive_check (lpp_shape_program ?SP) (lppssr_nonproductive evidence)"
    and shape_check: "lp_return_shape_program_check (lppssr_fuel evidence) (lppssr_grammar evidence)
      (lppssr_modes evidence) (lp_return_productive_program (lpp_shape_program ?SP) (lppssr_nonproductive evidence))"
    and seed_check: "lpp_shape_seed_check (lppssr_grammar evidence) G incoming_context (lppssr_seeds evidence)"
    using checked by (auto simp: lpp_control_shape_receipt_check_def)
  have seeds: "lp_return_shape_known (lppssr_grammar evidence) (lppssr_seeds evidence) eta"
    by (rule lpp_shape_seed_check_sound[OF seed_check _ lpp_stable_context_finite_envelope[OF compatible observed]])
      (use gr in auto)
  have shapes: "lp_return_shape_known (lppssr_grammar evidence) (lppssr_outputs evidence) theta"
    using lpp_control_stable_productive_shape_transfer[OF program builtin selected ordinary productive_check shape_check seeds shape_flow source_call] keep
    by (auto simp: lp_return_shape_known_def)
  have transfer: "lpp_check_transfer_program (lpp_transfer_lookup (lppsir_summaries ?model)) ?SP (lppsir_proofs ?model)"
    using base_checked by (auto simp: lpp_control_ground_receipt_check_def lpp_check_transfer_contract_def Let_def)
  have typing: "lpp_check_operation_context (lpp_transfer_lookup (lppsir_summaries ?model)) [(f,ts)]
      (fst (snd incoming_context)) (lppsir_facts ?model) (lppsir_integers ?model)"
    using checked prefix by (simp add: lpp_control_shape_receipt_check_def)
  have guards_after: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) theta)
      (fst (snd incoming_context))"
    using preserved by (cases incoming_context) (simp add: lpp_stable_context_holds_def lpp_evaluation_context_holds_def)
  have integers: "lpp_integer_known (lppsir_integers ?model) theta"
    by (rule lpp_checked_operation_context_evaluation[OF transfer typing guards_after _
      lpp_stable_evaluation_integer_contract[OF compatible]]) (use success in simp)
  have integer_ground: "\<forall>x\<in>set (lppsir_integers ?model). lp_seg_ground (theta x)"
    using integers by (auto simp: lpp_integer_known_def lpp_integer_value_def intro: lp_seg_ground.intros)
  have shape_ground: "\<forall>x\<in>set (map snd (filter (\<lambda>(shape,x). shape=LPReturnGround)
      (lppssr_outputs evidence))). lp_seg_ground (theta x)"
    using shapes by (fastforce simp: lp_return_shape_known_def lp_return_ground_exact)
  have cover: "set H \<subseteq> set G \<union> set ?K \<union> set (lppsir_integers ?model) \<union>
      set (map snd (filter (\<lambda>(shape,x). shape=LPReturnGround) (lppssr_outputs evidence)))"
    using checked by (simp add: lpp_control_shape_receipt_check_def)
  have ground: "lp_cut_knowledge (set H) [] theta"
    using cover outputs captured gr integer_ground shape_ground by (auto simp: lp_cut_knowledge_def)
  have final_context: "lpp_stable_context_holds operation SP
      (lpp_control_shape_context incoming_context evidence (f,ts)) theta"
    unfolding lpp_control_shape_context_def
    by (rule lpp_stable_add_shapes_sound[OF _ shapes]; rule lpp_stable_add_integers_sound[OF enriched integers])
  show ?thesis using rho ground final_context by blast
qed

end
