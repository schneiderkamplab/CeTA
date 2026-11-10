theory LP_Prolog_Control_Stable_Return
 imports LP_Prolog_Control_Return_Builtins LP_Prolog_Open_Stable_Return
begin

theorem lpp_control_stable_relational_return:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_control_return_program_check fuel P F SP"
    and builtins: "lpp_open_builtin_check F SP"
    and selected: "f\<in>F"
    and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''" "f\<noteq>''2:;''" "f\<noteq>''3:subtract''"
    and actual: "lpp_stable_actual_return operation P
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
  shows "lpp_guarded_success SP (lpp_stable_scalar_evaluation operation)
    (lpp_success_atom_eval (f,ts) rho)"
proof (rule lpp_control_relational_actual_return[where E="lpp_stable_scalar_evaluation operation",
      OF program lpp_control_stable_success_model[OF builtins] _ _ _
      lpp_stable_scalar_evaluation_subst selected ordinary actual])
  fix g us a keep sigma
  assume outcome: "lpp_stable_source_builtin operation g us (LPPBuiltinProbe a keep)"
    and model: "\<not>keep \<or> lpp_control_return_model (lpp_open_return_model F
      (lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation))) (lp_isubst a sigma)"
  show "lpp_control_return_model (lpp_open_return_model F
      (lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation)))
    (lp_isubst (LPIFun (LPCUser g) us) sigma)"
    by (rule lpp_control_stable_probe_model[OF builtins outcome])
next
  fix g us a sigma
  assume outcome: "lpp_stable_source_builtin operation g us (LPPBuiltinCall a)"
    and model: "lpp_control_return_model (lpp_open_return_model F
      (lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation))) (lp_isubst a sigma)"
  show "lpp_control_return_model (lpp_open_return_model F
      (lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation)))
    (lp_isubst (LPIFun (LPCUser g) us) sigma)"
    by (rule lpp_control_stable_call_model[where M="lpp_open_return_model F
      (lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation))", OF outcome model])
next
  fix g us cs ys ns sigma
  assume outcome: "lpp_stable_source_builtin operation g us (LPPBuiltinBranch cs ys ns)"
    and model: "list_all (lpc_model_goal (lpp_control_return_model (lpp_open_return_model F
        (lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation)))))
      (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) (cs@ys)) \<or>
      list_all (lpc_model_goal (lpp_control_return_model (lpp_open_return_model F
        (lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation)))))
      (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ns)"
  show "lpp_control_return_model (lpp_open_return_model F
      (lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation)))
    (lp_isubst (LPIFun (LPCUser g) us) sigma)"
    by (rule lpp_control_stable_branch_model[where M="lpp_open_return_model F
      (lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation))", OF outcome model])
qed

ML \<open>
val checked = [@{thm lpp_control_stable_relational_return}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable control return" else ();
\<close>
end
