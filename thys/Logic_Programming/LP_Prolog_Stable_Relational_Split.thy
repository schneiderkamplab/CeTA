theory LP_Prolog_Stable_Relational_Split
 imports LP_Prolog_Stable_Relational_Return
begin
hide_const (open) Tree_Automata_Containment.entry

theorem lpp_stable_guarded_relational_split_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and model: "lpp_inline_return_program_check P F SP"
    and builtins: "lpp_inline_builtin_check F SP"
    and selected: "f\<in>F" and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and pre: "lpcts_pre receipt=[LPCAtom (Fun (LPCUser f) ts)]"
    and subset: "set (lpcts_ground receipt) \<subseteq> set (lpcn_ground (lpctr_node entry))"
    and checked: "lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts
      incoming_context (lpp_context_add_success incoming_context (f,ts)) entry receipt"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and first_descent: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)\<in>R"
    and return_descent: "\<And>rho theta. lpp_stable_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho \<Longrightarrow>
      rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<Longrightarrow>
      lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<Longrightarrow>
      lpp_stable_context_holds operation SP (lpp_context_add_success incoming_context (f,ts)) theta \<Longrightarrow>
      (lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_second_in receipt) theta)\<in>R"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>R \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP contexts roots us b ret \<Longrightarrow> lpp_stable_triple_answer_contract operation P us Q ret"
  shows "lpp_stable_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof -
  show ?thesis
  proof (rule lpp_stable_guarded_split_interface_lower[OF compatible transfer checked program known observed free _ first_descent return_descent lower])
    fix rho
    assume actual: "lpp_stable_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho"
    obtain theta where rho: "rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta"
      and known_after: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) [] theta"
      and returned: "lpp_stable_context_holds operation SP
        (lpp_context_add_success incoming_context (f,ts)) theta"
      using lpp_stable_relational_receipt_return[OF model builtins selected ordinary pre known observed actual]
      by blast
    have ground: "lp_cut_knowledge (set (lpcts_ground receipt)) [] theta"
      using known_after subset by (auto simp: lp_cut_knowledge_def)
    show "\<exists>theta. rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<and>
      lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<and>
      lpp_stable_context_holds operation SP (lpp_context_add_success incoming_context (f,ts)) theta"
      using rho ground returned by blast
  qed
qed

lemma lpp_stable_relational_ground_receipt_return:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_finite_ground_receipt_check P incoming_context pre G H vs evidence"
    and model_identity: "lppsir_program (lppsgr_model evidence)=SP"
    and prefix: "pre=[LPCAtom (Fun (LPCUser f) ts)]"
    and known: "lp_cut_knowledge (set G) guards eta"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and actual: "lpp_stable_actual_return operation P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
  shows "\<exists>theta. rho=lpc_return_env (map Var vs) theta \<and>
    lp_cut_knowledge (set H) [] theta \<and>
    lpp_stable_context_holds operation SP (lpp_context_add_success (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) (f,ts)) theta"
proof -
  let ?model = "lppsgr_model evidence"
  let ?F = "set (lppsir_predicates ?model)"
  let ?SP = "lppsir_program ?model"
  let ?modes = "lppsgr_modes evidence"
  let ?K = "lppsgr_ground evidence"
  let ?G = "set G \<union> lpp_source_context_ground incoming_context"
  have selected: "f\<in>?F"
    and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and flow: "set ?K \<subseteq> lp_ground_flow ?modes [(LPCUser f,ts)] ?G"
    using checked prefix by (auto simp: lpp_finite_ground_receipt_check_def Let_def
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
      (use lpp_stable_actual_return_finite[OF source] in \<open>simp add: prefix\<close>)
  have outputs: "\<forall>x\<in>set ?K. lp_seg_ground (theta x)" using result flow by blast
  have preserved: "lpp_stable_context_holds operation SP incoming_context theta"
    by (rule lpp_stable_actual_return_preserves_context[OF source]) (use observed in simp)
  have next_context: "lpp_stable_context_holds operation SP (lpp_context_add_ground incoming_context ?K) theta"
    by (rule lpp_stable_add_ground_sound[OF preserved outputs])
  have captured: "theta x=eta x" if x: "x\<in>set G" for x
    using lpp_stable_seg_captured_term[OF source, of "Var x"] gr x by simp
  have ground: "lp_cut_knowledge (set H) [] theta"
    using cover outputs captured gr by (auto simp: lp_cut_knowledge_def)
  have relation: "lpp_guarded_success SP (lpp_stable_scalar_evaluation operation)
      (lpp_success_atom_eval (f,ts) theta)"
    using lpp_inline_stable_relational_return[OF program builtin selected ordinary]
      source model_identity by (simp add: prefix)
  have enriched: "lpp_stable_context_holds operation SP
      (lpp_context_add_success (lpp_context_add_ground incoming_context ?K) (f,ts)) theta"
    by (rule lpp_stable_add_success[OF next_context relation])
  show ?thesis using rho ground enriched by blast
qed


theorem lpp_stable_guarded_relational_ground_split_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and SP :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes compatible: "lpp_stable_integer_operations operation"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and ground_checked: "lpp_finite_ground_receipt_check P incoming_context
      (lpcts_pre receipt) (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt)
      (lpcn_vars (lpctr_node entry)) evidence"
    and model_identity: "lppsir_program (lppsgr_model evidence)=SP"
    and pre: "lpcts_pre receipt=[LPCAtom (Fun (LPCUser f) ts)]"
    and checked: "lpp_finite_triple_check_split_interface T first_types second_types fuel D Q roots contexts
      incoming_context (lpp_context_add_success (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) (f,ts)) entry receipt"
    and program: "lp_cut_source_program P"
    and known: "lp_cut_knowledge (set (lpcn_ground (lpctr_node entry))) (lpcn_guards (lpctr_node entry)) eta"
    and observed: "lpp_stable_context_holds operation SP incoming_context eta"
    and free: "lpc_free_knowledge (set (lpctr_free entry)) eta"
    and first_descent: "(lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_first_in receipt) eta)\<in>R"
    and return_descent: "\<And>rho theta. lpp_stable_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho \<Longrightarrow>
      rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<Longrightarrow>
      lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<Longrightarrow>
      lpp_stable_context_holds operation SP (lpp_context_add_success (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) (f,ts)) theta \<Longrightarrow>
      (lp_atom_eval (lpctr_input entry) eta,lp_atom_eval (lpcts_second_in receipt) theta)\<in>R"
    and lower: "\<And>us b ret. (lp_atom_eval (lpctr_input entry) eta,b)\<in>R \<Longrightarrow>
      lpp_stable_triple_root_rep operation SP contexts roots us b ret \<Longrightarrow> lpp_stable_triple_answer_contract operation P us Q ret"
  shows "lpp_stable_triple_answer_contract operation P (lpc_return_eval eta (lpc_triple_root_state entry)) Q
    (lp_atom_eval (lpctr_output entry))"
proof -
  show ?thesis
  proof (rule lpp_stable_guarded_split_interface_lower[OF compatible transfer checked program known observed free _ first_descent return_descent lower])
    fix rho
    assume actual: "lpp_stable_actual_return operation P
      (lpc_return_eval eta [(LPCGoals (lpcts_pre receipt),map Var (lpcn_vars (lpctr_node entry)))]) rho"
    obtain theta where rho: "rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta"
      and ground: "lp_cut_knowledge (set (lpcts_ground receipt)) [] theta"
      and returned: "lpp_stable_context_holds operation SP
        (lpp_context_add_success (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) (f,ts)) theta"
      using lpp_stable_relational_ground_receipt_return[OF compatible ground_checked model_identity pre known observed actual]
      by blast
    show "\<exists>theta. rho=lpc_return_env (map Var (lpcn_vars (lpctr_node entry))) theta \<and>
      lp_cut_knowledge (set (lpcts_ground receipt)) [] theta \<and>
      lpp_stable_context_holds operation SP (lpp_context_add_success (lpp_context_add_ground incoming_context (lppsgr_ground evidence)) (f,ts)) theta"
      using rho ground returned by blast
  qed
qed

ML \<open>
val checked = [@{thm lpp_stable_guarded_relational_ground_split_checked_lower}, @{thm lpp_stable_relational_ground_receipt_return}, @{thm lpp_stable_guarded_relational_split_checked_lower}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable relational Split dependency" else ();
\<close>
end
