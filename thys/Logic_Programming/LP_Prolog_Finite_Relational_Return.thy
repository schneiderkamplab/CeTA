theory LP_Prolog_Finite_Relational_Return
 imports LP_Prolog_Inline_Return_Builtins LP_Prolog_Finite_Actual_Contexts
begin

text \<open>A helper's actual successful return satisfies the complete guarded
source model, including evaluation relations. This is stronger than merely
retaining the output's integer type. It is independent of helper termination
and does not assert that every abstract model value is an actual return.\<close>

theorem lpp_inline_relational_actual_return:
  fixes P :: "(string,string) lp_cut_program"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_inline_return_program_check P F SP"
    and builtin: "\<And>f ts sigma. f\<in>F \<Longrightarrow> U f ts (LPPBuiltinSuccess sigma) \<Longrightarrow>
      lpp_inline_return_model SP E (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
    and no_probe: "\<And>f ts a keep. f\<in>F \<Longrightarrow> \<not>U f ts (LPPBuiltinProbe a keep)"
    and no_call: "\<And>f ts a. f\<in>F \<Longrightarrow> \<not>U f ts (LPPBuiltinCall a)"
    and no_branch: "\<And>f ts cs ys ns. f\<in>F \<Longrightarrow> \<not>U f ts (LPPBuiltinBranch cs ys ns)"
    and no_choice: "\<And>f ts left right. f\<in>F \<Longrightarrow> \<not>U f ts (LPPBuiltinChoice left right)"
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
  show ?thesis by (rule lpp_scoped_model_actual_return_without_probe[OF modeled builtin no_probe no_call no_branch no_choice
    lpp_inline_return_model_subst[where E=E, OF stable] known actual])
qed

theorem lpp_inline_finite_relational_return:
  fixes P :: "(string,string) lp_cut_program"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_inline_return_program_check P F SP"
    and builtins: "lpp_inline_builtin_check F SP"
    and selected: "f\<in>F" and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and actual: "lp_actual_answer (lpp_domain_answers P lpp_builtin_signature
      lpp_finite_source_builtin lpp_finite_source_domain)
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
  shows "lpp_guarded_success SP lpp_finite_evaluation_result (lpp_success_atom_eval (f,ts) rho)"
  by (rule lpp_inline_relational_actual_return[where E=lpp_finite_evaluation_result,
    OF program lpp_inline_builtin_model[OF builtins] lpp_inline_no_probe[OF builtins] lpp_inline_no_call[OF builtins] lpp_inline_no_branch[OF builtins] lpp_inline_no_choice[OF builtins]
      lpp_finite_evaluation_subst selected ordinary actual])

fun lpp_context_add_success where
  "lpp_context_add_success (ps,gs,observations) atom = (ps@[atom],gs,observations)"

lemma lpp_evaluation_add_success:
  "lpp_evaluation_context_holds E SP incoming_context eta \<Longrightarrow>
   lpp_guarded_success SP E (lpp_success_atom_eval atom eta) \<Longrightarrow>
   lpp_evaluation_context_holds E SP (lpp_context_add_success incoming_context atom) eta"
  by (cases incoming_context) (simp add: lpp_evaluation_context_holds_def)

text \<open>The caller's context is preserved on actual return. The relational
fact is appended only to the resumed successful continuation, never to a saved
failure alternative. Initialization and caller/callee renaming remain separate
obligations of the existing Split interface checker.\<close>

lemma lpp_finite_relational_return_context:
  fixes P :: "(string,string) lp_cut_program"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_inline_return_program_check P F SP"
    and builtins: "lpp_inline_builtin_check F SP"
    and selected: "f\<in>F" and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and observed: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming_context eta"
    and actual: "lpp_finite_actual_return P
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
  shows "lpp_evaluation_context_holds lpp_finite_evaluation_result SP
    (lpp_context_add_success incoming_context (f,ts)) rho"
proof -
  have preserved: "lpp_evaluation_context_holds lpp_finite_evaluation_result SP incoming_context rho"
    by (rule lpp_finite_actual_return_preserves_context[OF actual]) (use observed in simp)
  have returned: "lpp_guarded_success SP lpp_finite_evaluation_result (lpp_success_atom_eval (f,ts) rho)"
    by (rule lpp_inline_finite_relational_return[OF program builtins selected ordinary actual])
  show ?thesis by (rule lpp_evaluation_add_success[OF preserved returned])
qed

ML \<open>
val checked = [@{thm lpp_inline_finite_relational_return}, @{thm lpp_finite_relational_return_context}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted finite relational return" else ();
\<close>
end
