theory LP_Prolog_Triple_Integer_Return
 imports LP_Prolog_Triple_Split_Interface LP_Prolog_Source_Integer_Return
   LP_Prolog_Success_Transfer_XML
begin

hide_const (open) Tree_Automata_Containment.entry

record lpp_source_integer_receipt =
  lppsir_predicates :: "string list"
  lppsir_summaries :: "((string * nat) * (nat list * nat list) list) list"
  lppsir_program :: "string lpp_success_clause list"
  lppsir_proofs :: "(string lpp_transfer_fact list * string lpp_integer_output list) list list"
  lppsir_facts :: "string lpp_transfer_fact list"
  lppsir_integers :: "string list"

fun lpp_context_add_integers where
  "lpp_context_add_integers (ps,gs,obs) K =
    (ps,gs @ map (\<lambda>x. LPPSInteger (Var x)) K,
      obs @ map (\<lambda>x. LPPOInteger (Var x)) K)"

lemma lpp_context_add_integers_sound:
  "lpp_source_context_holds SP incoming_context eta \<Longrightarrow> lpp_integer_known K eta \<Longrightarrow>
    lpp_source_context_holds SP (lpp_context_add_integers incoming_context K) eta"
  by (cases incoming_context) (auto simp: lpp_path_context_holds_def lpp_integer_known_def lpp_is_integer_def list_all_iff)

fun lpp_source_integer_prefix_check where
  "lpp_source_integer_prefix_check F T guards facts K [LPCAtom (Fun (LPCUser f) ts)] =
    (f\<in>F \<and> lpp_check_operation_context T [(f,ts)] guards facts K)"
| "lpp_source_integer_prefix_check F T guards facts K _ = False"

definition lpp_source_integer_receipt_check where
  "lpp_source_integer_receipt_check P incoming_context pre G H vs evidence =
    (set (lppsir_integers evidence) \<subseteq> set vs \<and>
     set H \<subseteq> set G \<union> set (lppsir_integers evidence) \<and>
     lpp_source_return_program_check P (set (lppsir_predicates evidence)) (lppsir_program evidence) \<and>
     lpp_return_builtin_check (set (lppsir_predicates evidence)) (lppsir_program evidence) \<and>
     lpp_check_transfer_contract (lppsir_summaries evidence) (lppsir_program evidence) (lppsir_proofs evidence) \<and>
     lpp_source_integer_prefix_check (set (lppsir_predicates evidence))
       (lpp_transfer_lookup (lppsir_summaries evidence)) (fst (snd incoming_context))
       (lppsir_facts evidence) (lppsir_integers evidence) pre)"


lemma lpp_source_integer_receipt_return:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpp_source_integer_receipt_check P incoming_context pre G H vs evidence"
    and known: "lp_cut_knowledge (set G) guards eta"
    and observed: "lpp_source_context_holds SP incoming_context eta"
    and actual: "lpp_actual_return P (lpc_return_eval eta [(LPCGoals pre,map Var vs)]) rho"
  shows "\<exists>theta. rho=lpc_return_env (map Var vs) theta \<and>
    lp_cut_knowledge (set H) [] theta \<and>
    lpp_source_context_holds SP (lpp_context_add_integers incoming_context (lppsir_integers evidence)) theta"
proof -
  let ?F = "set (lppsir_predicates evidence)"
  let ?SP = "lppsir_program evidence"
  let ?T = "lpp_transfer_lookup (lppsir_summaries evidence)"
  let ?K = "lppsir_integers evidence"
  obtain f ts where pre: "pre=[LPCAtom (Fun (LPCUser f) ts)]"
    and selected: "f\<in>?F"
    and typing: "lpp_check_operation_context ?T [(f,ts)] (fst (snd incoming_context)) (lppsir_facts evidence) ?K"
    using checked by (auto simp: lpp_source_integer_receipt_check_def Let_def
      elim!: lpp_source_integer_prefix_check.elims)
  have program: "lpp_source_return_program_check P ?F ?SP"
    and builtin: "lpp_return_builtin_check ?F ?SP"
    and transfer: "lpp_check_transfer_program ?T ?SP (lppsir_proofs evidence)"
    and cover: "set H \<subseteq> set G \<union> set ?K"
    using checked by (auto simp: lpp_source_integer_receipt_check_def Let_def lpp_check_transfer_contract_def)
  obtain theta where source: "lpp_actual_return P [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) (LPCGoals pre),eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    using lpp_seg_observed_actual[OF actual] by blast
  have guards: "list_all (lpp_success_guard_holds lpp_integer_result eta) (fst (snd incoming_context))"
    using observed by (cases incoming_context) (simp add: lpp_path_context_holds_def)
  have integers: "lpp_integer_known ?K theta"
    by (rule lpp_source_integer_return[OF program builtin selected transfer typing guards])
      (use source in \<open>simp add: pre\<close>)
  have preserved: "lpp_source_context_holds SP incoming_context theta"
    by (rule lpp_actual_return_preserves_context[OF source]) (use observed in simp)
  have next_context: "lpp_source_context_holds SP (lpp_context_add_integers incoming_context ?K) theta"
    by (rule lpp_context_add_integers_sound[OF preserved integers])
  have gr: "\<forall>x\<in>set G. lp_seg_ground (eta x)" using known by (simp add: lp_cut_knowledge_def)
  have captured: "theta x=eta x" if x: "x\<in>set G" for x
    using lpp_seg_captured_term[OF source, of "Var x"] gr x by simp
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

definition lpp_triple_check_integer_split where
  "lpp_triple_check_integer_split fuel P D Q roots contexts incoming_context entry receipt evidence =
    (lpp_triple_check_split_interface fuel D Q roots contexts incoming_context
       (lpp_context_add_integers incoming_context (lppsir_integers evidence)) entry receipt \<and>
     lpp_source_integer_receipt_check P incoming_context (lpcts_pre receipt)
       (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt) (lpcn_vars (lpctr_node entry)) evidence)"

theorem lpp_triple_integer_split_checked_lower:
  fixes P :: "(string,string) lp_cut_program"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes checked: "lpp_triple_check_integer_split fuel P D Q roots contexts incoming_context entry receipt evidence"
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
    (lpp_context_add_integers incoming_context (lppsir_integers evidence)) entry receipt"
    and returns: "lpp_source_integer_receipt_check P incoming_context (lpcts_pre receipt)
      (lpcn_ground (lpctr_node entry)) (lpcts_ground receipt) (lpcn_vars (lpctr_node entry)) evidence"
    using checked by (auto simp: lpp_triple_check_integer_split_def)
  show ?thesis by (rule lpp_triple_split_interface_lower[OF interface program known observed free
    lpp_source_integer_receipt_return[OF returns known observed] lower])
qed

end
