theory LP_Prolog_Control_Actual_Return
 imports LP_Prolog_Control_Return_Cover
begin

text \<open>The control-aware logical cover is used only to describe actual
successful answers. Every termination and continuation obligation remains in
the existing answer-sensitive source composition.\<close>

theorem lpp_control_relational_actual_return:
  fixes P :: "(string,string) lp_cut_program"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
    and F SP E
  defines "M \<equiv> lpp_control_return_model (lpp_open_return_model F (lpp_inline_return_model SP E))"
  assumes program: "lpp_control_return_program_check fuel P F SP"
    and builtin: "\<And>f ts sigma. U f ts (LPPBuiltinSuccess sigma) \<Longrightarrow>
      M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and probe: "\<And>f ts a keep sigma. U f ts (LPPBuiltinProbe a keep) \<Longrightarrow>
      (\<not>keep \<or> M (lp_isubst a sigma)) \<Longrightarrow>
      M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and call: "\<And>f ts a sigma. U f ts (LPPBuiltinCall a) \<Longrightarrow>
      M (lp_isubst a sigma) \<Longrightarrow> M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and branch: "\<And>f ts cs ys ns sigma. U f ts (LPPBuiltinBranch cs ys ns) \<Longrightarrow>
      (list_all (lpc_model_goal M) (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) (cs@ys)) \<or>
       list_all (lpc_model_goal M) (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ns)) \<Longrightarrow>
      M (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and stable: "\<And>e t sigma. E e t \<Longrightarrow> E (lp_isubst e sigma) (lp_isubst t sigma)"
    and selected: "f\<in>F"
    and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''" "f\<noteq>''2:;''" "f\<noteq>''3:subtract''"
    and actual: "lp_actual_answer (lpp_domain_answers P B U D)
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
  shows "lpp_guarded_success SP E (lpp_success_atom_eval (f,ts) rho)"
proof -
  let ?gs = "[LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)]"
  let ?property = "\<lambda>theta. lpp_guarded_success SP E (lpp_success_atom_eval (f,ts) theta)"
  have modeled: "lpc_model_program P M"
    unfolding M_def by (rule lpp_control_return_program_sound[OF program])
  have stable_inline: "lpp_inline_return_model SP E (lp_isubst t sigma)"
    if "lpp_inline_return_model SP E t" for t sigma
    by (rule lpp_inline_return_model_subst[where SP=SP and E=E, OF stable that])
  have stable_open: "lpp_open_return_model F (lpp_inline_return_model SP E) (lp_isubst t sigma)"
    if "lpp_open_return_model F (lpp_inline_return_model SP E) t" for t sigma
    by (rule lpp_open_return_model_subst[where M="lpp_inline_return_model SP E", OF stable_inline that])
  have stable_model: "M (lp_isubst t sigma)" if "M t" for t sigma
  proof -
    have source_model: "lpp_control_return_model (lpp_open_return_model F (lpp_inline_return_model SP E)) t"
      using that unfolding M_def .
    show ?thesis unfolding M_def
      by (rule lpp_control_return_subst[where M="lpp_open_return_model F (lpp_inline_return_model SP E)",
        OF stable_open source_model])
  qed
  have initial: "lpc_model_goals M ?property ?gs eta"
    by (auto simp: lpc_model_goals_def M_def selected ordinary
      lpp_control_return_ordinary lpp_success_atom_eval_def lp_ieval_subst map_map o_def)
  have known: "list_all (lpc_model_frame M ?property) [(LPCGoals ?gs,eta)]"
    using initial by simp
  show ?thesis by (rule lpp_model_actual_return[OF modeled builtin probe call branch stable_model known actual])
qed

ML \<open>
val checked = [@{thm lpp_control_relational_actual_return}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted control actual return" else ();
\<close>
end
