theory LP_Prolog_Inline_Probe_Return
 imports LP_Prolog_Finite_Relational_Return
begin

text \<open>Successful helper relations can include probes when both the
returned model and the probe call closure are justified. Probe termination
remains a source graph obligation; this theorem grants no termination result.\<close>

theorem lpp_inline_relational_actual_return_with_probes:
  fixes P :: "(string,string) lp_cut_program"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_inline_return_program_check P F SP"
    and builtin: "\<And>f ts sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinSuccess sigma) \<Longrightarrow>
      lpp_inline_return_model SP E (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and probe_model: "\<And>f ts a keep sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinProbe a keep) \<Longrightarrow>
      (\<not>keep \<or> lpp_inline_return_model SP E (lp_isubst a sigma)) \<Longrightarrow>
      lpp_inline_return_model SP E (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and probe_control: "\<And>f ts a keep. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinProbe a keep) \<Longrightarrow>
      lpc_return_control_igoal F (LPCAtom a)"
    and call_model: "\<And>f ts a sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinCall a) \<Longrightarrow>
      lpp_inline_return_model SP E (lp_isubst a sigma) \<Longrightarrow> lpp_inline_return_model SP E (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and branch_model: "\<And>f ts cs ys ns sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinBranch cs ys ns) \<Longrightarrow>
      (list_all (lpc_model_goal (lpp_inline_return_model SP E)) (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) (cs@ys)) \<or>
       list_all (lpc_model_goal (lpp_inline_return_model SP E)) (map (lp_cut_map (\<lambda>t. lp_isubst t sigma)) ns)) \<Longrightarrow>
      lpp_inline_return_model SP E (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and call_control: "\<And>f ts a. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinCall a) \<Longrightarrow>
      lpc_return_control_igoal F (LPCAtom a)"
    and branch_control: "\<And>f ts cs ys ns. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinBranch cs ys ns) \<Longrightarrow>
      list_all (lpc_return_control_igoal F) (cs@ys@ns)"
    and stable: "\<And>e t sigma. E e t \<Longrightarrow> E (lp_isubst e sigma) (lp_isubst t sigma)"
    and selected: "f\<in>F" and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and actual: "lp_actual_answer (lpp_domain_answers P B U D)
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
  shows "lpp_guarded_success SP E (lpp_success_atom_eval (f,ts) rho)"
proof -
  let ?M = "lpp_inline_return_model SP E"
  let ?gs = "[LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)]"
  let ?property = "\<lambda>theta. lpp_guarded_success SP E (lpp_success_atom_eval (f,ts) theta)"
  have modeled: "lpc_scoped_model_program P F ?M"
    by (rule lpp_inline_return_program_sound[OF program])
  have initial: "lpc_model_goals ?M ?property ?gs eta"
    by (auto simp: lpc_model_goals_def ordinary lpp_success_atom_eval_def
      lp_ieval_subst map_map o_def)
  have known: "list_all (lpc_scoped_model_frame F ?M ?property) [(LPCGoals ?gs,eta)]"
    using selected initial by simp
  show ?thesis by (rule lpp_scoped_model_actual_return[OF modeled builtin probe_model probe_control call_model branch_model call_control branch_control
    lpp_inline_return_model_subst[where E=E, OF stable] known actual])
qed

ML \<open>
val checked = [@{thm lpp_inline_relational_actual_return_with_probes}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted probe relational return" else ();
\<close>
end
