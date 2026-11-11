theory LP_Prolog_Stopped_Triple_Observed
  imports LP_Prolog_Stopped_Control LP_Prolog_Stable_Triple_Observed
begin

fun lpp_stopped_emit_action where
  "lpp_stopped_emit_action (Some (LPPSControl action)) = Some action"
| "lpp_stopped_emit_action _ = None"

lemma lpp_stopped_triple_instance_stable:
  fixes a :: "(string lp_cut_symbol,string) lp_iatom"
    and inp :: "(string lp_cut_symbol,nat) lp_atom"
  shows "lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B) ss ev tt \<Longrightarrow>
    lpc_triple_instance_invariant a inp ss \<Longrightarrow> lpc_triple_instance_invariant a inp tt"
  by (auto simp: lp_answer_stop_def lpc_triple_instance_invariant_def
    dest: lpp_domain_triple_instance_stable[unfolded lpc_triple_instance_invariant_def] split: if_splits)

definition lpp_stopped_triple_answer_contract where
  "lpp_stopped_triple_answer_contract operation P ss Q ret =
    lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature))
      ss ({} :: bool rel) False (\<lambda>eta. \<not>lp_answer_model Q (ret eta))"

theorem lpp_stopped_triple_observed_control_contexts:
  fixes SP :: "string lpp_success_clause list"
    and a :: "(string lp_cut_symbol,string) lp_iatom"
    and inp :: "(string lp_cut_symbol,nat) lp_atom"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_stopped_control_contexts fuel P C nds states contexts local_contexts Fs T returned arity actions"
    and enrich: "\<And>i eta. i<length nds \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
      lpp_stable_context_holds operation SP (local_contexts!i) eta"
    and ranked: "lpc_seg_ranked_control rank_of C"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and program: "lp_cut_source_program P"
    and invariant: "lpc_triple_instance_invariant a inp ss"
    and represented: "lpp_stable_module_rep operation SP nds states contexts Fs ss control"
    and boundary: "\<And>i eta. i<length nds \<Longrightarrow> actions!i=None \<Longrightarrow>
      lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta \<Longrightarrow>
      lpp_stable_context_holds operation SP (contexts!i) eta \<Longrightarrow>
      lpc_free_knowledge (set (Fs!i)) eta \<Longrightarrow>
      lpc_triple_instance_invariant a inp (lpc_return_eval eta (states!i)) \<Longrightarrow>
      lpp_stopped_triple_answer_contract operation P (lpc_return_eval eta (states!i)) Q (lp_atom_eval out)"
    and emits: "\<And>i. i<length nds \<Longrightarrow>
      lpp_finite_triple_check_emit fuel (nds!i) (lpp_stopped_emit_action (actions!i)) Q out (states!i) (fst (emissions!i)) (snd (emissions!i))"
  shows "lpp_stopped_triple_answer_contract operation P ss Q (lp_atom_eval out)"
  unfolding lpp_stopped_triple_answer_contract_def
proof (rule lpp_stopped_control_contract_contexts[where J="lpc_triple_instance_invariant a inp",
    OF compatible checked enrich ranked transfer program invariant lpp_stopped_triple_instance_stable
      lpp_triple_instance_frames lpc_triple_instance_subset lpc_triple_instance_scopes represented])
  fix i eta assume index: "i<length nds" and boundary_node: "actions!i=None"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and observed: "lpp_stable_context_holds operation SP (contexts!i) eta"
    and free: "lpc_free_knowledge (set (Fs!i)) eta"
    and inv: "lpc_triple_instance_invariant a inp (lpc_return_eval eta (states!i))"
  show "lp_answer_contract (lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature))
    (lpc_return_eval eta (states!i)) ({} :: bool rel) False (\<lambda>eta. \<not>lp_answer_model Q (lp_atom_eval out eta))"
    using boundary[OF index boundary_node known observed free inv]
    by (simp only: lpp_stopped_triple_answer_contract_def)
next
  fix i eta rho tt assume index: "i<length nds"
    and inv: "lpc_triple_instance_invariant a inp (lpc_return_eval eta (states!i))"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!i))) (lpcn_guards (nds!i)) eta"
    and event: "lp_answer_stop (lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain) (lpp_undefined_answer_stop P lpp_builtin_signature)
      (lpc_return_eval eta (states!i)) (Some rho) tt"
  have original: "lpp_domain_answers P lpp_builtin_signature (lpp_stable_source_builtin operation) lpp_finite_source_domain (lpc_return_eval eta (states!i)) (Some rho) tt"
    using event by (auto simp: lp_answer_stop_def split: if_splits)
  show "(False,\<not>lp_answer_model Q (lp_atom_eval out rho))\<in>({} :: bool rel)\<^sup>*"
    using lpp_finite_triple_checked_emit[OF emits[OF index] known original] by simp
qed

ML \<open>
val checked = [@{thm lpp_stopped_triple_observed_control_contexts}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stopped observed triple dependency" else ();
\<close>
end
