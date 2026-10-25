theory LP_Cut_SEG_Triple_Prefix
  imports LP_Cut_SEG_Triple_Receipt LP_Cut_Return_Preserved_Ground
begin

text \<open>A successful-prefix fact must follow the same answer environment
through continuation execution. In particular, saved alternatives retain their
own fact instance. Substitution closure is sufficient; groundness is not.\<close>

lemma lpc_answer_substitution_property:
  assumes stable: "\<And>eta sigma. F eta \<Longrightarrow> F (\<lambda>x. lp_isubst (eta x) sigma)"
    and step: "lpc_answer_transition P ss event us"
    and known: "list_all (\<lambda>e. F (snd e)) ss"
  shows "list_all (\<lambda>e. F (snd e)) us \<and>
    (\<forall>eta. event=Some eta \<longrightarrow> F eta)"
  using step known
  by (cases rule: lpc_answer_transition.cases)
    (auto simp: list_all_iff intro: stable
      dest: subsetD[OF lpc_answer_prune_set_subset])

lemma lpc_actual_return_substitution_property:
  assumes stable: "\<And>eta sigma. F eta \<Longrightarrow> F (\<lambda>x. lp_isubst (eta x) sigma)"
    and actual: "lpc_actual_return P ss eta"
    and known: "list_all (\<lambda>e. F (snd e)) ss"
  shows "F eta"
proof -
  obtain us tail where path: "(ss,us)\<in>(lpc_answer_steps P)\<^sup>*"
    and event: "lpc_answer_transition P us (Some eta) tail"
    using actual by (auto simp: lpc_actual_return_def)
  have preserved: "list_all (\<lambda>e. F (snd e)) us"
    using path
  proof (induct rule: rtrancl_induct)
    case base show ?case by (rule known)
  next
    case (step ys zs)
    obtain ev where local: "lpc_answer_transition P ys ev zs"
      using step.hyps(2) by (auto simp: lpc_answer_steps_def)
    show ?case using lpc_answer_substitution_property[where F=F, OF stable local step.hyps(3)] by blast
  qed
  show ?thesis using lpc_answer_substitution_property[where F=F, OF stable event preserved] by simp
qed

lemma lpc_actual_return_preserves_model:
  assumes actual: "lpc_actual_return P ss eta"
    and known: "list_all (\<lambda>e. lp_answer_model Q (lp_atom_eval a (snd e))) ss"
  shows "lp_answer_model Q (lp_atom_eval a eta)"
proof (rule lpc_actual_return_substitution_property[OF _ actual known])
  fix rho sigma assume model: "lp_answer_model Q (lp_atom_eval a rho)"
  show "lp_answer_model Q (lp_atom_eval a (\<lambda>x. lp_isubst (rho x) sigma))"
    using lp_answer_model_subst[OF model, of sigma]
    by (simp add: lp_atom_eval_def lp_iatom_subst_def lp_ieval_subst map_map o_def)
qed

theorem lpc_triple_answer_extend_facts:
  assumes child: "lpc_triple_answer_contract P ss Q (lp_atom_eval out)"
    and known: "list_all (\<lambda>e. list_all (\<lambda>a. lp_answer_model Q (lp_atom_eval a (snd e))) facts) ss"
    and receipt: "lpc_triple_check_model_clause Q (out#facts) final c bindings"
  shows "lpc_triple_answer_contract P ss Q (lp_atom_eval final)"
proof (unfold lpc_triple_answer_contract_def, intro conjI allI impI)
  show "SN_on (lp_cut_mgu_source P) {map fst ss}"
    by (rule lpc_triple_answer_contract_SN[OF child])
next
  fix eta assume actual: "lpc_actual_return P ss eta"
  have result_model: "lp_answer_model Q (lp_atom_eval out eta)"
    by (rule lpc_triple_answer_contract_return[OF child actual])
  have preserved: "lp_answer_model Q (lp_atom_eval a eta)" if "a\<in>set facts" for a
    by (rule lpc_actual_return_preserves_model[OF actual])
      (use known that in \<open>auto simp: list_all_iff\<close>)
  show "lp_answer_model Q (lp_atom_eval final eta)"
    by (rule lpc_triple_checked_model_clause[OF receipt]) (use result_model preserved in auto)
qed

end
