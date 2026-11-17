theory LP_Prolog_Finite_Local_Triple_Observed
 imports LP_Prolog_Finite_Local_Control LP_Prolog_Stable_Triple_Observed
begin

theorem lpp_finite_local_triple_observed_control:
  fixes SP :: "string lpp_success_clause list"
    and a :: "(string lp_cut_symbol,string) lp_iatom"
    and inp :: "(string lp_cut_symbol,nat) lp_atom"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_finite_direct_control_contexts fuel P C nds states contexts local_contexts Fs T returned arity actions"
    and enrich: "\<And>i eta. i<length nds \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
      lpp_stable_context_holds operation SP (local_contexts!i) eta"
    and ranked: "lpc_seg_ranked_control rank_of C"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
    and finite: "lpp_finite_direct_invariant A ss"
    and local_states: "lpp_check_local_finite_states A P nds states local_contexts"
    and signature: "\<And>f n. (f,n)\<in>A \<Longrightarrow> (f,n)\<in>lpp_builtin_signature \<Longrightarrow> lpp_direct_arithmetic_name f"
    and invariant: "lpc_triple_instance_invariant a inp ss"
    and represented: "lpp_stable_module_rep operation SP nds states contexts Fs ss control"
    and boundary: "\<And>i eta. i<length nds \<Longrightarrow> actions!i=None \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
      lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
      lpp_finite_direct_invariant A (lpc_return_eval eta (states!i)) \<Longrightarrow>
      lpc_triple_instance_invariant a inp (lpc_return_eval eta (states!i)) \<Longrightarrow>
      lpp_stable_triple_answer_contract operation P (lpc_return_eval eta (states!i)) Q (lp_atom_eval out)"
    and emits: "\<And>i. i<length nds \<Longrightarrow>
      lpp_finite_triple_check_emit fuel (nds!i) (actions!i) Q out (states!i) (fst (emissions!i)) (snd (emissions!i))"
  shows "lpp_stable_triple_answer_contract operation P ss Q (lp_atom_eval out)"
  unfolding lpp_stable_triple_answer_contract_def
proof (rule lpp_finite_direct_control_invariant_contract_contexts[where K="lpc_triple_instance_invariant a inp",
    OF compatible checked enrich ranked transfer program finite invariant
      lpp_triple_instance_frames lpc_triple_instance_subset lpc_triple_instance_scopes
      lpp_domain_triple_instance_stable _ represented]; (assumption)?)
 fix i eta event tt
 assume index: "i<length nds"
   and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
   and observed: "lpp_stable_context_holds operation SP (local_contexts!i) eta"
   and free: "lpc_free_knowledge (set (Fs!i)) eta"
   and current: "lpp_finite_direct_invariant A (lpc_return_eval eta (states!i))"
   and step: "lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation)
     lpp_finite_source_domain (lpc_return_eval eta (states!i)) event tt"
 show "lpp_finite_direct_invariant A tt"
   by (rule lpp_checked_local_finite_stable[OF compatible local_states signature index known observed current step])
next
  fix i eta assume index: "i<length nds" and boundary_node: "actions!i=None"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
    and free: "lpc_free_knowledge (set (Fs!i)) eta"
    and current: "lpp_finite_direct_invariant A (lpc_return_eval eta (states!i))"
    and inv: "lpc_triple_instance_invariant a inp (lpc_return_eval eta (states!i))"
  show "lp_answer_contract (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain)
    (lpc_return_eval eta (states!i)) ({} :: bool rel) False (\<lambda>eta. \<not>lp_answer_model Q (lp_atom_eval out eta))"
    using boundary[OF index boundary_node known observed free current inv]
    by (simp only: lpp_stable_triple_answer_contract_def)
next
  fix i eta rho tt assume index: "i<length nds"
    and inv: "lpp_finite_direct_invariant A (lpc_return_eval eta (states!i))"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and event: "lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain
      (lpc_return_eval eta (states!i)) (Some rho) tt"
  show "(False,\<not>lp_answer_model Q (lp_atom_eval out rho))\<in>({} :: bool rel)\<^sup>*"
    using lpp_finite_triple_checked_emit[OF emits[OF index] known event] by simp
qed

ML \<open>
val checked = [@{thm lpp_finite_local_triple_observed_control}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite local triple control" else ();
\<close>
end
