theory LP_Prolog_Triple_Free_Observed
 imports LP_Prolog_Context_Free_Control LP_Prolog_Triple_Observed
begin

theorem lpp_triple_free_observed_control:
  fixes SP :: "string lpp_success_clause list"
    and a :: "(string lp_cut_symbol,string) lp_iatom"
    and inp :: "(string lp_cut_symbol,nat) lp_atom"
  assumes checked: "lpp_check_context_free_control fuel P C nds states contexts Fs T typings returned arity actions"
    and ranked: "lpc_seg_ranked_control rank_of C"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
    and invariant: "lpc_triple_instance_invariant a inp ss"
    and represented: "lpp_context_free_module_rep SP nds states contexts Fs ss control"
    and boundary: "\<And>i eta. i<length nds \<Longrightarrow> actions!i=None \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpp_source_context_holds SP (contexts!i) eta \<Longrightarrow>
      lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
      lpc_triple_instance_invariant a inp (lpc_return_eval eta (states!i)) \<Longrightarrow>
      lpp_triple_answer_contract P (lpc_return_eval eta (states!i)) Q (lp_atom_eval out)"
    and emits: "\<And>i. i<length nds \<Longrightarrow>
      lpc_triple_check_emit Q out (states!i) (fst (emissions!i)) (snd (emissions!i))"
  shows "lpp_triple_answer_contract P ss Q (lp_atom_eval out)"
  unfolding lpp_triple_answer_contract_return_contract
proof (rule lpp_context_free_observed_control_contract[where J="lpc_triple_instance_invariant a inp",
    OF checked ranked transfer program invariant lpp_domain_triple_instance_stable
      lpc_triple_instance_subset lpc_triple_instance_scopes represented])
  fix i eta assume index: "i<length nds" and boundary_node: "actions!i=None"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and observed: "lpp_source_context_holds SP (contexts!i) eta"
    and free: "lpc_free_knowledge (set (Fs!i)) eta"
    and inv: "lpc_triple_instance_invariant a inp (lpc_return_eval eta (states!i))"
  show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    (lpc_return_eval eta (states!i)) ({} :: bool rel) False (\<lambda>eta. \<not>lp_answer_model Q (lp_atom_eval out eta))"
    using boundary[OF index boundary_node known observed free inv]
    by (simp only: lpp_triple_answer_contract_return_contract)
next
  fix i eta rho tt assume index: "i<length nds"
    and inv: "lpc_triple_instance_invariant a inp (lpc_return_eval eta (states!i))"
    and event: "lpp_domain_answers P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain
      (lpc_return_eval eta (states!i)) (Some rho) tt"
  show "(False,\<not>lp_answer_model Q (lp_atom_eval out rho))\<in>({} :: bool rel)\<^sup>*"
    using lpp_triple_checked_emit[OF emits[OF index] event] by simp
qed

end
