theory LP_Prolog_Source_Integer_Return
 imports LP_Prolog_Source_Return_Builtins LP_Prolog_Actual_Returns LP_Prolog_Operation_Context
begin

text \<open>This contract concerns actual successful returns of a source helper.
Its proof uses every reachable defining clause and the fixed builtin semantics.
It makes no termination claim, including for recursive or divergent helpers.\<close>

theorem lpp_source_integer_return:
  fixes P :: "(string,string) lp_cut_program"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_source_return_program_check P F SP"
    and builtins: "lpp_return_builtin_check F SP"
    and selected: "f\<in>F"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and typing: "lpp_check_operation_context T [(f,ts)] guards facts K"
    and guards: "list_all (lpp_success_guard_holds lpp_integer_result eta) guards"
    and actual: "lpp_actual_return P
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
  shows "lpp_integer_known K rho"
proof -
  let ?M = "lpp_source_return_model SP"
  let ?gs = "[LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)]"
  have modeled: "lpc_scoped_model_program P F ?M"
    by (rule lpp_source_return_program_sound[OF program])
  have initial: "lpc_model_goals ?M (lpp_integer_known K) ?gs eta"
  proof (unfold lpc_model_goals_def, intro conjI allI impI)
    show "list_all lpc_model_safe_goal ?gs" by simp
  next
    fix sigma assume model: "list_all (lpc_model_goal ?M)
      (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs)"
    have success: "list_all (lpp_guarded_success SP lpp_integer_result)
      (map (\<lambda>b. lpp_success_atom_eval b (\<lambda>x. lp_isubst (eta x) sigma)) [(f,ts)])"
      using model by (simp add: lpp_success_atom_eval_def lp_ieval_subst map_map o_def)
    have observed: "list_all (lpp_success_guard_holds lpp_integer_result
      (\<lambda>x. lp_isubst (eta x) sigma)) guards"
      using guards by (auto simp: list_all_iff intro: lpp_success_guard_integer_subst)
    show "lpp_integer_known K (\<lambda>x. lp_isubst (eta x) sigma)"
      by (rule lpp_checked_operation_context[OF transfer typing observed success])
  qed
  have known: "list_all (lpc_scoped_model_frame F ?M (lpp_integer_known K)) [(LPCGoals ?gs,eta)]"
    using selected initial by simp
  show ?thesis by (rule lpp_scoped_model_actual_return[OF modeled
    lpp_return_builtin_model[OF builtins] lpp_source_return_model_subst known actual])
qed

ML \<open>
val checked = [@{thm lpp_source_integer_return}, @{thm lpp_source_return_program_sound},
  @{thm lpp_return_builtin_model}, @{thm lpp_scoped_model_actual_return}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted source integer return dependency" else ();
\<close>
end
