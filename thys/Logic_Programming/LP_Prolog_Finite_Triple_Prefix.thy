theory LP_Prolog_Finite_Triple_Prefix
 imports LP_Prolog_Finite_Triple_Answers LP_Cut_SEG_Triple_Receipt
begin

lemma lpp_finite_actual_return_preserves_model:
  assumes actual: "lpp_finite_actual_return P ss eta"
    and known: "list_all (\<lambda>e. lp_answer_model Q (lp_atom_eval a (snd e))) ss"
  shows "lp_answer_model Q (lp_atom_eval a eta)"
proof (rule lpp_actual_return_substitution_property[OF _ actual known])
  fix rho sigma assume model: "lp_answer_model Q (lp_atom_eval a rho)"
  show "lp_answer_model Q (lp_atom_eval a (\<lambda>x. lp_isubst (rho x) sigma))"
    using lp_answer_model_subst[OF model, of sigma]
    by (simp add: lp_atom_eval_def lp_iatom_subst_def lp_ieval_subst map_map o_def)
qed

theorem lpp_finite_triple_answer_extend_facts:
  assumes child: "lpp_finite_triple_answer_contract P ss Q (lp_atom_eval out)"
    and known: "list_all (\<lambda>e. list_all (\<lambda>a. lp_answer_model Q (lp_atom_eval a (snd e))) facts) ss"
    and receipt: "lpc_triple_check_model_clause Q (out#facts) final c bindings"
  shows "lpp_finite_triple_answer_contract P ss Q (lp_atom_eval final)"
proof (unfold lpp_finite_triple_answer_contract_def, intro conjI allI impI)
  show "SN_on (lp_answer_steps (lpp_domain_answers P lpp_builtin_signature lpp_finite_source_builtin lpp_finite_source_domain)) {ss}"
    using child by (simp add: lpp_finite_triple_answer_contract_def)
next
  fix eta assume actual: "lpp_finite_actual_return P ss eta"
  have result_model: "lp_answer_model Q (lp_atom_eval out eta)"
    by (rule lpp_finite_triple_answer_contract_return[OF child actual])
  have preserved: "lp_answer_model Q (lp_atom_eval a eta)" if "a\<in>set facts" for a
    by (rule lpp_finite_actual_return_preserves_model[OF actual])
      (use known that in \<open>auto simp: list_all_iff\<close>)
  show "lp_answer_model Q (lp_atom_eval final eta)"
    by (rule lpc_triple_checked_model_clause[OF receipt]) (use result_model preserved in auto)
qed

end
