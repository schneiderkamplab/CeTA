theory LP_Prolog_Inline_Return_Builtins
 imports LP_Prolog_Inline_Return_Model LP_Prolog_Finite_Source LP_Prolog_Source_Return_Builtins
begin

definition lpp_inline_builtin_check where
  "lpp_inline_builtin_check F SP = (\<forall>(f,n)\<in>lpp_builtin_signature.
    f\<in>F \<and> f\<noteq>''2:is'' \<and> f\<noteq>''1:integer'' \<longrightarrow>
      (((f,lpp_return_builtin_args n),[],[])\<in>set SP \<or>
       (f=''2:length'' \<and> n=2 \<and>
        ((f,lpp_return_builtin_args 2),[],[LPPSInteger (Var ''xx'')])\<in>set SP)))"

lemma lpp_inline_builtin_model:
  assumes checked: "lpp_inline_builtin_check F SP"
    and reachable: "f\<in>F"
    and outcome: "lpp_finite_source_builtin f ts (LPPBuiltinSuccess sigma)"
  shows "lpp_inline_return_model SP lpp_finite_evaluation_result
    (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
proof (cases "f=''2:is''")
  case True
  have length: "length ts=2" and success: "lpp_finite_is_outcome (ts!0) (ts!1) (LPPBuiltinSuccess sigma)"
    using outcome by (auto simp: lpp_finite_source_builtin_def True)
  have result: "lpp_finite_evaluation_result (ts!1) (lp_isubst (ts!0) sigma)"
    and fixed: "lp_isubst (ts!1) sigma=ts!1"
    using lpp_finite_is_success_evidence[OF success] by auto
  show ?thesis using result fixed by (simp add: True length)
next
  case no_is: False
  show ?thesis
  proof (cases "f=''1:integer''")
    case True
    have old: "lpp_integer_source_builtin ''1:integer'' ts (LPPBuiltinSuccess sigma)"
      using outcome by (simp add: lpp_finite_source_builtin_def True)
    show ?thesis using old
      by (auto simp: True lpp_integer_test_outcome_def split: if_splits)
  next
    case no_integer: False
    let ?us = "map (\<lambda>t. lp_isubst t sigma) ts"
    let ?eta = "\<lambda>v. ?us!(length v-1)"
    have selected: "(f,length ts)\<in>lpp_builtin_signature"
      by (rule lpp_finite_source_selected[OF outcome])
    obtain guards where clause: "((f,lpp_return_builtin_args (length ts)),[],guards)\<in>set SP"
      and holds: "list_all (lpp_success_guard_holds lpp_finite_evaluation_result ?eta) guards"
    proof (cases "((f,lpp_return_builtin_args (length ts)),[],[])\<in>set SP")
      case True
      show ?thesis by (rule that[OF True]) simp
    next
      case False
      have name: "f=''2:length''" and arity: "length ts=2"
        and typed: "((f,lpp_return_builtin_args 2),[],[LPPSInteger (Var ''xx'')])\<in>set SP"
        using checked selected reachable no_is no_integer False
        by (auto simp: lpp_inline_builtin_check_def)
      have success: "lpp_finite_length_outcome (ts!0) (ts!1) (LPPBuiltinSuccess sigma)"
        using outcome by (simp add: lpp_finite_source_builtin_def name)
      have integer: "lpp_is_integer (lp_isubst (ts!1) sigma)"
        by (rule lpp_finite_length_success_integer[OF success])
      have guard: "list_all (lpp_success_guard_holds lpp_finite_evaluation_result ?eta)
        [LPPSInteger (Var ''xx'')]" using integer arity by simp
      show ?thesis using that[of "[LPPSInteger (Var ''xx'')]"] typed arity guard by simp
    qed
    have success: "lpp_guarded_success SP lpp_finite_evaluation_result
      (lpp_success_atom_eval (f,lpp_return_builtin_args (length ts)) ?eta)"
      by (rule lpp_guarded_success.clause[OF clause holds]) simp
    have instantiated: "map (\<lambda>t. lp_ieval t ?eta) (lpp_return_builtin_args (length ts))=?us"
      using lpp_return_builtin_args_eval[of ?us] by simp
    have result: "lpp_guarded_success SP lpp_finite_evaluation_result (f,?us)"
      using success by (simp only: lpp_success_atom_eval_def fst_conv snd_conv instantiated)
    show ?thesis using result by (simp add: no_is no_integer)
  qed
qed

theorem lpp_inline_finite_integer_return:
  fixes P :: "(string,string) lp_cut_program"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
  assumes program: "lpp_inline_return_program_check P F SP"
    and builtins: "lpp_inline_builtin_check F SP"
    and selected: "f\<in>F" and ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and transfer: "lpp_check_transfer_program T SP receipts"
    and typing: "lpp_check_operation_context T [(f,ts)] guards facts K"
    and guards: "list_all (lpp_success_guard_holds lpp_finite_evaluation_result eta) guards"
    and actual: "lp_actual_answer (lpp_domain_answers P lpp_builtin_signature
      lpp_finite_source_builtin lpp_finite_source_domain)
      [(LPCGoals [LPCAtom (lp_ieval (Fun (LPCUser f) ts) eta)],eta)] rho"
  shows "lpp_integer_known K rho"
  by (rule lpp_inline_integer_actual_return[where E=lpp_finite_evaluation_result,
      OF program lpp_inline_builtin_model[OF builtins]
      lpp_finite_evaluation_subst lpp_finite_evaluation_integer_contract selected ordinary transfer typing guards actual])

ML \<open>
val checked = [@{thm lpp_inline_finite_integer_return}, @{thm lpp_inline_builtin_model},
  @{thm lpp_finite_source_checked_step}, @{thm lpp_scalar_unifier_mgu}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted finite evaluation return dependency" else ();
\<close>
end
