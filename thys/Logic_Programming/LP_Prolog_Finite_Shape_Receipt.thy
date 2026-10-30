theory LP_Prolog_Finite_Shape_Receipt
  imports LP_Prolog_Shape_Observations LP_Prolog_Finite_Ground_Receipt LP_Prolog_Finite_Integer_Receipt
begin

record lpp_source_shape_receipt =
  lppssr_ground :: lpp_source_ground_receipt
  lppssr_fuel :: nat
  lppssr_grammar :: "string lp_cut_symbol lp_return_grammar"
  lppssr_modes :: "(string lp_cut_symbol \<times> lp_return_shape list \<times> lp_return_shape list) list"
  lppssr_seeds :: "(lp_return_shape \<times> string) list"
  lppssr_outputs :: "(lp_return_shape \<times> string) list"

fun lpp_finite_shape_prefix_check where
  "lpp_finite_shape_prefix_check F shape_fuel grammar modes seeds outputs [LPCAtom (Fun (LPCUser f) ts)] =
    (f\<in>F \<and> f\<noteq>''2:is'' \<and> f\<noteq>''1:integer'' \<and>
      (case lp_return_shape_transfer shape_fuel grammar modes (LPCUser f,ts) (Some seeds) of
        None \<Rightarrow> False | Some result \<Rightarrow> set outputs \<subseteq> set result))"
| "lpp_finite_shape_prefix_check F shape_fuel grammar modes seeds outputs _ = False"

definition lpp_shape_receipt_context where
  "lpp_shape_receipt_context incoming evidence =
    lpp_context_add_shapes
      (lpp_context_add_integers
        (lpp_context_add_ground incoming (lppsgr_ground (lppssr_ground evidence)))
        (lppsir_integers (lppsgr_model (lppssr_ground evidence))))
      (lppssr_grammar evidence) (lppssr_outputs evidence)"

definition lpp_finite_shape_receipt_check where
  "lpp_finite_shape_receipt_check P incoming pre G H vs evidence =
    (let base_return=lppssr_ground evidence; model=lppsgr_model base_return in
      lpp_finite_ground_receipt_check P incoming pre G G vs base_return \<and>
      lpp_finite_integer_receipt_check P incoming pre G G vs model \<and>
      set (map snd (lppssr_outputs evidence)) \<subseteq> set vs \<and>
      set H \<subseteq> set G \<union> set (lppsgr_ground base_return) \<union> set (lppsir_integers model) \<union>
        set (map snd (filter (\<lambda>(s,x). s=LPReturnGround) (lppssr_outputs evidence))) \<and>
      lp_return_shape_program_check (lppssr_fuel evidence) (lppssr_grammar evidence)
        (lppssr_modes evidence) (lpp_shape_program (lppsir_program model)) \<and>
      lpp_shape_seed_check (lppssr_grammar evidence) G incoming (lppssr_seeds evidence) \<and>
      lpp_finite_shape_prefix_check (set (lppsir_predicates model)) (lppssr_fuel evidence)
        (lppssr_grammar evidence) (lppssr_modes evidence) (lppssr_seeds evidence)
        (lppssr_outputs evidence) pre)"

lemma lpp_finite_shape_receipt_return:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpp_finite_shape_receipt_check P incoming pre G H vs evidence"
    and known: "lp_cut_knowledge (set G) guards eta"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming eta"
    and actual: "lpp_finite_actual_return P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
  shows "\<exists>theta. rho=lpc_return_env (map Var vs) theta \<and>
    lp_cut_knowledge (set H) [] theta \<and>
    lpp_evaluation_context_holds lpp_finite_evaluation_result SP (lpp_shape_receipt_context incoming evidence) theta"
proof -
  let ?ground = "lppssr_ground evidence"
  let ?model = "lppsgr_model ?ground"
  let ?F = "set (lppsir_predicates ?model)"
  let ?SP = "lppsir_program ?model"
  let ?grammar = "lppssr_grammar evidence"
  let ?T = "lpp_transfer_lookup (lppsir_summaries ?model)"
  let ?known = "set G \<union> lpp_source_context_ground incoming"
  obtain f ts result where pre: "pre=[LPCAtom (Fun (LPCUser f) ts)]"
    and selected: "f\<in>?F" and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and flow: "lp_return_shape_transfer (lppssr_fuel evidence) ?grammar (lppssr_modes evidence)
      (LPCUser f,ts) (Some (lppssr_seeds evidence))=Some result"
    and keep: "set (lppssr_outputs evidence) \<subseteq> set result"
    using checked by (auto simp: lpp_finite_shape_receipt_check_def Let_def
      elim!: lpp_finite_shape_prefix_check.elims split: option.splits)
  have ground_check: "lpp_finite_ground_receipt_check P incoming pre G G vs ?ground"
    and integer_check: "lpp_finite_integer_receipt_check P incoming pre G G vs ?model"
    and shape_check: "lp_return_shape_program_check (lppssr_fuel evidence) ?grammar
      (lppssr_modes evidence) (lpp_shape_program ?SP)"
    and seed_check: "lpp_shape_seed_check ?grammar G incoming (lppssr_seeds evidence)"
    and cover: "set H \<subseteq> set G \<union> set (lppsgr_ground ?ground) \<union> set (lppsir_integers ?model) \<union>
      set (map snd (filter (\<lambda>(s,x). s=LPReturnGround) (lppssr_outputs evidence)))"
    using checked by (auto simp: lpp_finite_shape_receipt_check_def Let_def)
  have program: "lpp_inline_return_program_check P ?F ?SP"
    and builtin: "lpp_inline_builtin_check ?F ?SP"
    and ground_modes: "lpp_guarded_ground_check ?SP (lppsgr_modes ?ground)"
    and ground_flow: "set (lppsgr_ground ?ground) \<subseteq> lp_ground_flow (lppsgr_modes ?ground) [(LPCUser f,ts)] ?known"
    using ground_check by (auto simp: lpp_finite_ground_receipt_check_def Let_def pre)
  have transfer: "lpp_check_transfer_program ?T ?SP (lppsir_proofs ?model)"
    and typing: "lpp_check_operation_context ?T [(f,ts)] (fst (snd incoming))
      (lppsir_facts ?model) (lppsir_integers ?model)"
    using integer_check by (auto simp: lpp_finite_integer_receipt_check_def lpp_check_transfer_contract_def pre)
  obtain theta where source: "lpp_finite_actual_return P [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) (LPCGoals pre),eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    using lpp_finite_seg_observed_actual[OF actual] by blast
  have actual_source: "lp_actual_answer (lpp_domain_answers P lpp_builtin_signature
    lpp_finite_source_builtin lpp_finite_source_domain)
    [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] theta"
    using source by (simp add: pre)
  have gr: "\<forall>x\<in>?known. lp_seg_ground (eta x)"
    using known lpp_evaluation_context_ground_sound[OF lpp_finite_evaluation_ground observed]
    by (auto simp: lp_cut_knowledge_def)
  have returned_ground: "\<forall>x\<in>set (lppsgr_ground ?ground). lp_seg_ground (theta x)"
    using lpp_inline_guarded_ground_return[OF program builtin selected ordinary ground_modes gr actual_source]
      ground_flow by blast
  have source_guards: "list_all (lpp_success_guard_holds lpp_finite_evaluation_result eta) (fst (snd incoming))"
    using observed by (cases incoming) (simp add: lpp_evaluation_context_holds_def)
  have returned_integers: "lpp_integer_known (lppsir_integers ?model) theta"
    by (rule lpp_inline_finite_integer_return[OF program builtin selected ordinary transfer typing source_guards actual_source])
  have seeds: "lp_return_shape_known ?grammar (lppssr_seeds evidence) eta"
    by (rule lpp_shape_seed_check_sound[OF seed_check _ observed]) (use gr in auto)
  have shapes: "lp_return_shape_known ?grammar (lppssr_outputs evidence) theta"
    using lpp_inline_shape_return[OF program builtin selected ordinary shape_check seeds flow actual_source] keep
    by (auto simp: lp_return_shape_known_def)
  have preserved: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming theta"
    by (rule lpp_finite_actual_return_preserves_context[OF source]) (use observed in simp)
  have next_context: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP (lpp_shape_receipt_context incoming evidence) theta"
    unfolding lpp_shape_receipt_context_def
    by (rule lpp_evaluation_add_shapes_sound[OF _ shapes];
        rule lpp_evaluation_add_integers_sound[OF _ returned_integers];
        rule lpp_evaluation_add_ground_sound[OF preserved returned_ground])
  have captured: "theta x=eta x" if "x\<in>set G" for x
    using lpp_finite_seg_captured_term[OF source, of "Var x"] gr that by simp
  have integer_ground: "\<forall>x\<in>set (lppsir_integers ?model). lp_seg_ground (theta x)"
    using returned_integers by (auto simp: lpp_integer_known_def lpp_integer_value_def intro: lp_seg_ground.intros)
  have shape_ground: "\<forall>x\<in>set (map snd (filter (\<lambda>(s,x). s=LPReturnGround) (lppssr_outputs evidence))).
      lp_seg_ground (theta x)"
    using shapes by (fastforce simp: lp_return_shape_known_def lp_return_ground_exact)
  have preserved_ground: "\<forall>x\<in>set G. lp_seg_ground (theta x)"
    using gr captured by auto
  have ground: "lp_cut_knowledge (set H) [] theta"
    using cover preserved_ground returned_ground integer_ground shape_ground
    by (auto simp: lp_cut_knowledge_def)
  show ?thesis using rho ground next_context by blast
qed

ML \<open>
val audited = [@{thm lpp_inline_shape_return}, @{thm lpp_shape_seed_check_sound},
  @{thm lpp_finite_shape_receipt_return}];
val names = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = names [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof audited orelse
  exists (fn n => not (member (op =) inherited n)) (names audited)
  then error "Untrusted actual helper shape-return dependency" else ();
\<close>

end
