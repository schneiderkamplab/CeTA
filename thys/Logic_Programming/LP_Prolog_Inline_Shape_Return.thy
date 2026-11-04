theory LP_Prolog_Inline_Shape_Return
  imports LP_Prolog_Return_Shapes LP_Prolog_Guarded_Ground_Return
begin

lemma lp_return_shape_known_subst:
  fixes eta :: "'v \<Rightarrow> ('f,'w) lp_iterm"
    and sigma :: "'w \<Rightarrow> ('f,'w) lp_iterm"
  assumes known: "lp_return_shape_known G facts eta"
  shows "lp_return_shape_known G facts (\<lambda>x. lp_isubst (eta x) sigma)"
  using known by (auto simp: lp_return_shape_known_def intro: lp_return_shape_subst)

theorem lpp_inline_shape_return:
  fixes P :: "(string,string) lp_cut_program"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_inline_return_program_check P F SP"
    and builtins: "lpp_inline_builtin_check F SP"
    and selected: "f\<in>F" and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and modes: "lp_return_shape_program_check shape_fuel G contracts (lpp_shape_program SP)"
    and known: "lp_return_shape_known G seeds eta"
    and flow: "lp_return_shape_transfer shape_fuel G contracts (LPCUser f,ts) (Some seeds)=Some outputs"
    and actual: "lp_actual_answer (lpp_domain_answers P lpp_builtin_signature
      lpp_finite_source_builtin lpp_finite_source_domain)
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
  shows "lp_return_shape_known G outputs rho"
proof -
  let ?M = "lpp_inline_return_model SP lpp_finite_evaluation_result :: (string lp_cut_symbol,string) lp_iterm \<Rightarrow> bool"
  let ?gs = "[LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)]"
  let ?property = "\<lambda>nu. lp_return_shape_known G outputs nu"
  have modeled: "lpc_scoped_model_program P F ?M"
    by (rule lpp_inline_return_program_sound[OF program])
  have initial_model: "lpc_model_goals ?M ?property ?gs eta"
  proof (unfold lpc_model_goals_def, intro conjI allI impI)
    show "list_all lpc_model_safe_goal ?gs" by simp
  next
    fix sigma assume model: "list_all (lpc_model_goal ?M)
      (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs)"
    let ?nu = "\<lambda>x. lp_isubst (eta x) sigma"
    have success: "lpp_guarded_success SP lpp_finite_evaluation_result
      (lpp_success_atom_eval (f,ts) ?nu)"
      using model by (simp add: ordinary lpp_success_atom_eval_def lp_ieval_subst map_map o_def)
    have contract: "lp_return_contracts G contracts (lp_atom_eval (LPCUser f,ts) ?nu)"
      using lpp_guarded_return_shape_contracts[OF modes success]
      by (simp add: lpp_lift_iatom_def lpp_success_atom_eval_def lp_atom_eval_def)
    have preserved: "lp_return_shape_known G seeds ?nu"
      by (rule lp_return_shape_known_subst[OF known])
    have valid: "lp_return_facts_valid G ?nu
      (lp_return_shape_transfer shape_fuel G contracts (LPCUser f,ts) (Some seeds))"
      by (rule lp_return_shape_transfer_sound[OF contract])
        (use preserved in \<open>simp add: lp_return_facts_valid_def\<close>)
    show "?property ?nu" using valid[unfolded flow] by (simp add: lp_return_facts_valid_def)
  qed
  have frames: "list_all (lpc_scoped_model_frame F ?M ?property) [(LPCGoals ?gs,eta)]"
    using selected initial_model by simp
  show ?thesis by (rule lpp_scoped_model_actual_return_without_probe[OF modeled
    lpp_inline_builtin_model[OF builtins] lpp_inline_no_probe[OF builtins] lpp_inline_return_model_subst[where E=lpp_finite_evaluation_result, OF lpp_finite_evaluation_subst] frames actual])
qed

end
