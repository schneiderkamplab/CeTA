theory LP_Prolog_Inline_Ground_Return
 imports LP_Prolog_Inline_Return_Builtins LP_Answer_Groundness
begin

text \<open>Finite-ground output contracts reuse the shared clause-cover checker.
The erased success model covers actual successful source returns, independently
of termination. Its runtime terms may be rational; finite groundness is never
inferred merely from a finite representation of such a term.\<close>

theorem lpp_inline_ground_return:
  fixes P :: "(string,string) lp_cut_program"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_inline_return_program_check P F SP"
    and builtins: "lpp_inline_builtin_check F SP"
    and selected: "f\<in>F" and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and modes: "lp_ground_check (lpp_erase_success SP) contracts"
    and known: "\<forall>x\<in>G. lp_seg_ground (eta x)"
    and actual: "lp_actual_answer (lpp_domain_answers P lpp_builtin_signature
      lpp_finite_source_builtin lpp_finite_source_domain)
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
  shows "\<forall>x\<in>lp_ground_flow contracts [(LPCUser f,ts)] G. lp_seg_ground (rho x)"
proof -
  let ?M = "lpp_inline_return_model SP lpp_finite_evaluation_result :: (string lp_cut_symbol,string) lp_iterm \<Rightarrow> bool"
  let ?gs = "[LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)]"
  let ?H = "lp_ground_flow contracts [(LPCUser f,ts)] G"
  let ?property = "\<lambda>nu. \<forall>x\<in>?H. lp_seg_ground (nu x)"
  have modeled: "lpc_scoped_model_program P F ?M"
    by (rule lpp_inline_return_program_sound[OF program])
  have initial: "lpc_model_goals ?M ?property ?gs eta"
  proof (unfold lpc_model_goals_def, intro conjI allI impI)
    show "list_all lpc_model_safe_goal ?gs" by simp
  next
    fix sigma assume model: "list_all (lpc_model_goal ?M)
      (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ?gs)"
    let ?nu = "\<lambda>x. lp_isubst (eta x) sigma"
    have success: "lpp_guarded_success SP lpp_finite_evaluation_result
      (lpp_success_atom_eval (f,ts) ?nu)"
      using model by (simp add: ordinary lpp_success_atom_eval_def lp_ieval_subst map_map o_def)
    have erased: "lp_answer_model (lpp_erase_success SP) (lp_atom_eval (LPCUser f,ts) ?nu)"
      using lpp_guarded_success_erases[OF success]
      by (simp add: lpp_lift_iatom_def lpp_success_atom_eval_def lp_atom_eval_def)
    have valid: "list_all lp_ground_valid_mode contracts"
      using modes by (simp add: lp_ground_check_def)
    have contracts: "\<forall>a\<in>set [(LPCUser f,ts)]. \<forall>m\<in>set contracts.
      lp_ground_contract m (lp_atom_eval a ?nu)"
      using lp_ground_check_model[OF modes erased] by simp
    have preserved: "\<forall>x\<in>G. lp_seg_ground (?nu x)"
      using known by (simp add: lp_seg_ground_subst)
    show "?property ?nu" by (rule lp_ground_flow_sound[OF valid contracts preserved])
  qed
  have frames: "list_all (lpc_scoped_model_frame F ?M ?property) [(LPCGoals ?gs,eta)]"
    using selected initial by simp
  show ?thesis by (rule lpp_scoped_model_actual_return_without_probe[OF modeled
    lpp_inline_builtin_model[OF builtins] lpp_inline_no_probe[OF builtins] lpp_inline_no_call[OF builtins] lpp_inline_no_branch[OF builtins] lpp_inline_no_choice[OF builtins] lpp_inline_return_model_subst[where E=lpp_finite_evaluation_result, OF lpp_finite_evaluation_subst] frames actual])
qed

ML \<open>
val checked = [@{thm lpp_inline_ground_return}, @{thm lp_ground_check_model}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted source ground-return dependency" else ();
\<close>
end
