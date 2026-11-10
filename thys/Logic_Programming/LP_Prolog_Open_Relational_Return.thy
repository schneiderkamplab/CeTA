theory LP_Prolog_Open_Relational_Return
 imports LP_Prolog_Open_Return_Program
begin


theorem lpp_open_relational_actual_return:
  fixes P :: "(string,string) lp_cut_program"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_inline_return_program_check P F SP"
    and safe: "\<And>c. c<length P \<Longrightarrow> list_all lpc_model_safe_goal (snd (P!c))"
    and heads: "\<And>c. c<length P \<Longrightarrow> \<exists>g us. fst (P!c)=Fun (LPCUser g) us"
    and builtin: "\<And>f ts sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinSuccess sigma) \<Longrightarrow>
      lpp_inline_return_model SP E (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and probe_model: "\<And>f ts a keep sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinProbe a keep) \<Longrightarrow>
      (\<not>keep \<or> lpp_open_return_model F (lpp_inline_return_model SP E) (lp_isubst a sigma)) \<Longrightarrow>
      lpp_inline_return_model SP E (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and call_model: "\<And>f ts a sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinCall a) \<Longrightarrow>
      lpp_open_return_model F (lpp_inline_return_model SP E) (lp_isubst a sigma) \<Longrightarrow>
      lpp_inline_return_model SP E (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and branch_model: "\<And>f ts cs ys ns sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinBranch cs ys ns) \<Longrightarrow>
      (list_all (lpc_model_goal (lpp_open_return_model F (lpp_inline_return_model SP E)))
        (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) (cs@ys)) \<or>
       list_all (lpc_model_goal (lpp_open_return_model F (lpp_inline_return_model SP E)))
        (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ns)) \<Longrightarrow>
      lpp_inline_return_model SP E (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and stable: "\<And>e t sigma. E e t \<Longrightarrow> E (lp_isubst e sigma) (lp_isubst t sigma)"
    and selected: "f\<in>F" and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and actual: "lp_actual_answer (lpp_domain_answers P B U D)
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
  shows "lpp_guarded_success SP E (lpp_success_atom_eval (f,ts) rho)"
proof -
  let ?M = "lpp_open_return_model F (lpp_inline_return_model SP E)"
  let ?gs = "[LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)]"
  let ?property = "\<lambda>theta. lpp_guarded_success SP E (lpp_success_atom_eval (f,ts) theta)"
  have scoped: "lpc_scoped_model_program P F (lpp_inline_return_model SP E)"
    by (rule lpp_inline_return_program_sound[OF program])
  have modeled: "lpc_model_program P ?M"
    by (rule lpp_open_return_program[OF scoped safe heads])
  have builtin_open: "?M (lp_isubst (LPIFun (LPCUser g) us) sigma)"
    if "U g us (LPPBuiltinSuccess sigma)" for g us sigma
    using builtin[OF _ that] by (cases "g\<in>F") auto
  have probe_open: "?M (lp_isubst (LPIFun (LPCUser g) us) sigma)"
    if "U g us (LPPBuiltinProbe a keep)" and "\<not>keep \<or> ?M (lp_isubst a sigma)"
    for g us a keep sigma
    using probe_model[OF _ that] by (cases "g\<in>F") auto
  have call_open: "?M (lp_isubst (LPIFun (LPCUser g) us) sigma)"
    if "U g us (LPPBuiltinCall a)" and "?M (lp_isubst a sigma)"
    for g us a sigma
    using call_model[OF _ that] by (cases "g\<in>F") auto
  have branch_open: "?M (lp_isubst (LPIFun (LPCUser g) us) sigma)"
    if "U g us (LPPBuiltinBranch cs ys ns)" and
      "list_all (lpc_model_goal ?M) (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) (cs@ys)) \<or>
       list_all (lpc_model_goal ?M) (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ns)"
    for g us cs ys ns sigma
    using branch_model[OF _ that] by (cases "g\<in>F") auto
  have stable_open: "?M (lp_isubst t sigma)" if "?M t" for t sigma
    by (rule lpp_open_return_model_subst[OF lpp_inline_return_model_subst[where E=E, OF stable] that])
  have initial: "lpc_model_goals ?M ?property ?gs eta"
    by (auto simp: lpc_model_goals_def selected ordinary lpp_success_atom_eval_def
      lp_ieval_subst map_map o_def)
  have known: "list_all (lpc_model_frame ?M ?property) [(LPCGoals ?gs,eta)]"
    using selected initial by simp
  show ?thesis by (rule lpp_model_actual_return[OF modeled builtin_open probe_open call_open branch_open stable_open known actual])
qed

ML \<open>
val checked = [@{thm lpp_open_relational_actual_return}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted open relational return" else ();
\<close>
end
