theory LP_Prolog_Open_Stable_Return
 imports LP_Prolog_Open_Return_Builtins
begin

theorem lpp_open_stable_relational_return:
  fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_inline_return_program_check P F SP"
    and safe: "\<And>c. c<length P \<Longrightarrow> list_all lpc_model_safe_goal (snd (P!c))"
    and heads: "\<And>c. c<length P \<Longrightarrow> \<exists>g us. fst (P!c)=Fun (LPCUser g) us"
    and builtins: "lpp_open_builtin_check F SP"
    and selected: "f\<in>F" and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and actual: "lpp_stable_actual_return operation P
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
  shows "lpp_guarded_success SP (lpp_stable_scalar_evaluation operation) (lpp_success_atom_eval (f,ts) rho)"
proof (rule lpp_open_relational_actual_return[where E="lpp_stable_scalar_evaluation operation",
    OF program safe heads lpp_open_stable_builtin_model[OF builtins]
      _ _ _ _ lpp_stable_scalar_evaluation_subst selected ordinary actual])
  fix g us a keep sigma
  assume member: "g\<in>F" and outcome: "lpp_stable_source_builtin operation g us (LPPBuiltinProbe a keep)"
    and model: "\<not>keep \<or> lpp_open_return_model F
      (lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation)) (lp_isubst a sigma)"
  show "lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation)
    (lp_isubst (LPIFun (LPCUser g) us) sigma)"
    by (rule lpp_open_stable_probe_model[OF builtins member outcome])
next
  fix g us a sigma
  assume member: "g\<in>F" and outcome: "lpp_stable_source_builtin operation g us (LPPBuiltinCall a)"
    and model: "lpp_open_return_model F
      (lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation)) (lp_isubst a sigma)"
  show "lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation)
    (lp_isubst (LPIFun (LPCUser g) us) sigma)"
    by (rule lpp_open_stable_control_model[OF builtins member outcome]) auto
next
  fix g us cs ys ns sigma
  assume member: "g\<in>F" and outcome: "lpp_stable_source_builtin operation g us (LPPBuiltinBranch cs ys ns)"
    and model: "list_all (lpc_model_goal (lpp_open_return_model F
        (lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation))))
      (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) (cs@ys)) \<or>
      list_all (lpc_model_goal (lpp_open_return_model F
        (lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation))))
      (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ns)"
  show "lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation)
    (lp_isubst (LPIFun (LPCUser g) us) sigma)"
    by (rule lpp_open_stable_control_model[OF builtins member outcome]) auto
next
  fix g us left right sigma
  assume member: "g\<in>F" and outcome: "lpp_stable_source_builtin operation g us (LPPBuiltinChoice left right)"
    and model: "list_all (lpc_model_goal (lpp_open_return_model F
        (lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation))))
      (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) left) \<or>
      list_all (lpc_model_goal (lpp_open_return_model F
        (lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation))))
      (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) right)"
  show "lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation)
    (lp_isubst (LPIFun (LPCUser g) us) sigma)"
    by (rule lpp_open_stable_control_model[OF builtins member outcome]) auto
qed

lemma lpp_open_stable_ground_flow:
  assumes compatible: "lpp_stable_integer_operations operation"
    and modes: "lpp_guarded_ground_check SP contracts"
    and success: "lpp_guarded_success SP (lpp_stable_scalar_evaluation operation)
      (lpp_success_atom_eval (f,ts) rho)"
    and known: "\<forall>x\<in>G. lp_seg_ground (rho x)"
  shows "\<forall>x\<in>lp_ground_flow contracts [(LPCUser f,ts)] G. lp_seg_ground (rho x)"
proof -
  have evaluation: "lp_seg_ground e \<and> lp_seg_ground t"
    if "lpp_stable_scalar_evaluation operation e t" for e t
    using lpp_finite_evaluation_ground[OF lpp_stable_evaluation_finite_envelope[OF compatible that]] .
  have valid: "list_all lp_ground_valid_mode contracts"
    using modes by (simp add: lpp_guarded_ground_check_def)
  have contracts: "\<forall>a\<in>set [(LPCUser f,ts)]. \<forall>m\<in>set contracts.
    lp_ground_contract m (lp_atom_eval a rho)"
    using lpp_guarded_ground_check_model[OF modes evaluation success]
    by (simp add: lpp_lift_iatom_def lpp_success_atom_eval_def lp_atom_eval_def)
  show ?thesis by (rule lp_ground_flow_sound[OF valid contracts known])
qed

ML \<open>
val checked = [@{thm lpp_open_stable_relational_return},@{thm lpp_open_stable_ground_flow}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted open stable return" else ();
\<close>
end
