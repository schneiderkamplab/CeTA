theory LP_Prolog_Actual_Contexts
 imports LP_Prolog_Triple_Captured LP_Prolog_Guarded_Returns
begin

lemma lpp_source_context_holds_subst:
  fixes eta :: "'v \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
    and sigma :: "'w \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
  assumes known: "lpp_source_context_holds SP incoming_context eta"
  shows "lpp_source_context_holds SP incoming_context (\<lambda>x. lp_isubst (eta x) sigma)"
  using known
  by (cases incoming_context) (auto simp: lpp_path_context_holds_def list_all_iff
      lpp_success_atom_eval_subst[symmetric]
    intro: lpp_guarded_success_integer_subst lpp_success_guard_integer_subst
      lpp_numeric_observation_subst)

lemma lpp_actual_return_preserves_context:
  assumes actual: "lpp_actual_return P ss eta"
    and initialized: "list_all (\<lambda>frame. lpp_source_context_holds SP incoming_context (snd frame)) ss"
  shows "lpp_source_context_holds SP incoming_context eta"
  by (rule lpp_actual_return_substitution_property[OF lpp_source_context_holds_subst actual initialized])

lemma lpp_observed_actual_context:
  assumes actual: "lpp_actual_return P (lpc_return_eval eta [(e,map Var vs)]) rho"
    and known: "lpp_source_context_holds SP incoming_context eta"
  obtains theta where
    "rho=lpc_return_env (map Var vs) theta"
    "lpp_source_context_holds SP incoming_context theta"
proof -
  obtain theta where source: "lpp_actual_return P
      [(lp_cut_entry_map (\<lambda>t. lp_ieval t eta) e,eta)] theta"
    and rho: "rho=lpc_return_env (map Var vs) theta"
    using lpp_seg_observed_actual[OF actual] by blast
  have result: "lpp_source_context_holds SP incoming_context theta"
    by (rule lpp_actual_return_preserves_context[OF source]) (use known in simp)
  show ?thesis using that rho result by blast
qed

end
