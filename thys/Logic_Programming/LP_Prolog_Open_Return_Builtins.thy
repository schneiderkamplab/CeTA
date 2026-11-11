theory LP_Prolog_Open_Return_Builtins
 imports LP_Prolog_Open_Relational_Return LP_Prolog_Stable_Relational_Return
begin

definition lpp_open_builtin_check where
  "lpp_open_builtin_check F SP = (\<forall>(f,n)\<in>lpp_builtin_signature.
    f\<in>F \<and> f\<noteq>''2:is'' \<and> f\<noteq>''1:integer'' \<longrightarrow>
      (((f,lpp_return_builtin_args n),[],[])\<in>set SP \<or>
       (f=''2:length'' \<and> n=2 \<and>
        ((f,lpp_return_builtin_args 2),[],[LPPSInteger (Var ''xx'')])\<in>set SP)))"

lemma lpp_open_stable_builtin_model:
  assumes checked: "lpp_open_builtin_check F SP"
    and reachable: "f\<in>F"
    and outcome: "lpp_stable_source_builtin operation f ts (LPPBuiltinSuccess sigma)"
  shows "lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation)
    (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
proof (cases "f=''2:is''")
  case True
  have length: "length ts=2" and success: "lpp_stable_is_outcome operation (ts!0) (ts!1) (LPPBuiltinSuccess sigma)"
    using outcome by (auto simp: lpp_stable_source_builtin_def lpp_finite_source_builtin_def True)
  have result: "(lpp_stable_scalar_evaluation operation) (ts!1) (lp_isubst (ts!0) sigma)"
    and fixed: "lp_isubst (ts!1) sigma=ts!1"
    using lpp_stable_is_success_evidence[OF success] by auto
  show ?thesis using result fixed by (simp add: True length)
next
  case no_is: False
  show ?thesis
  proof (cases "f=''1:integer''")
    case True
    have old: "lpp_integer_source_builtin ''1:integer'' ts (LPPBuiltinSuccess sigma)"
      using lpp_stable_source_refines_finite[OF outcome] by (simp add: lpp_finite_source_builtin_def True)
    show ?thesis using old
      by (auto simp: True lpp_integer_test_outcome_def split: if_splits)
  next
    case no_integer: False
    let ?us = "map (\<lambda>t. lp_isubst t sigma) ts"
    let ?eta = "\<lambda>v. ?us!(length v-1)"
    have selected: "(f,length ts)\<in>lpp_builtin_signature"
      by (rule lpp_finite_source_selected[OF lpp_stable_source_refines_finite[OF outcome]])
    obtain guards where clause: "((f,lpp_return_builtin_args (length ts)),[],guards)\<in>set SP"
      and holds: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) ?eta) guards"
    proof (cases "((f,lpp_return_builtin_args (length ts)),[],[])\<in>set SP")
      case True
      show ?thesis by (rule that[OF True]) simp
    next
      case False
      have name: "f=''2:length''" and arity: "length ts=2"
        and typed: "((f,lpp_return_builtin_args 2),[],[LPPSInteger (Var ''xx'')])\<in>set SP"
        using checked selected reachable no_is no_integer False
        by (auto simp: lpp_open_builtin_check_def)
      have success: "lpp_finite_length_outcome (ts!0) (ts!1) (LPPBuiltinSuccess sigma)"
        using lpp_stable_source_refines_finite[OF outcome] by (simp add: lpp_finite_source_builtin_def name)
      have integer: "lpp_is_integer (lp_isubst (ts!1) sigma)"
        by (rule lpp_finite_length_success_integer[OF success])
      have guard: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) ?eta)
        [LPPSInteger (Var ''xx'')]" using integer arity by simp
      show ?thesis using that[of "[LPPSInteger (Var ''xx'')]"] typed arity guard by simp
    qed
    have success: "lpp_guarded_success SP (lpp_stable_scalar_evaluation operation)
      (lpp_success_atom_eval (f,lpp_return_builtin_args (length ts)) ?eta)"
      by (rule lpp_guarded_success.clause[OF clause holds]) simp
    have instantiated: "map (\<lambda>t. lp_ieval t ?eta) (lpp_return_builtin_args (length ts))=?us"
      using lpp_return_builtin_args_eval[of ?us] by simp
    have result: "lpp_guarded_success SP (lpp_stable_scalar_evaluation operation) (f,?us)"
      using success by (simp only: lpp_success_atom_eval_def fst_conv snd_conv instantiated)
    show ?thesis using result by (simp add: no_is no_integer)
  qed
qed

lemma lpp_open_stable_probe_model:
  assumes checked: "lpp_open_builtin_check F SP"
    and reachable: "f\<in>F"
    and outcome: "lpp_stable_source_builtin operation f ts (LPPBuiltinProbe a keep)"
  shows "lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation)
    (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
proof -
  have finite: "lpp_finite_source_builtin f ts (LPPBuiltinProbe a keep)"
    by (rule lpp_stable_source_refines_finite[OF outcome])
  have probe: "lpp_probe_name f" by (rule lpp_finite_source_probe_name[OF finite])
  have selected: "(f,length ts)\<in>lpp_builtin_signature"
    by (rule lpp_finite_source_selected[OF finite])
  have excluded: "\<not>lpp_probe_name ''2:is''" "\<not>lpp_probe_name ''1:integer''" "\<not>lpp_probe_name ''2:length''"
    by code_simp+
  have ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''" "f\<noteq>''2:length''"
    using probe excluded by blast+
  have clause: "((f,lpp_return_builtin_args (length ts)),[],[])\<in>set SP"
    using checked selected reachable ordinary by (auto simp: lpp_open_builtin_check_def)
  let ?us = "map (\<lambda>t. lp_isubst t sigma) ts"
  let ?eta = "\<lambda>v. ?us!(length v-1)"
  have success: "lpp_guarded_success SP (lpp_stable_scalar_evaluation operation)
    (lpp_success_atom_eval (f,lpp_return_builtin_args (length ts)) ?eta)"
    by (rule lpp_guarded_success.clause[OF clause]) simp_all
  have instantiated: "map (\<lambda>t. lp_ieval t ?eta) (lpp_return_builtin_args (length ts))=?us"
    using lpp_return_builtin_args_eval[of ?us] by simp
  have result: "lpp_guarded_success SP (lpp_stable_scalar_evaluation operation) (f,?us)"
    using success by (simp only: lpp_success_atom_eval_def fst_conv snd_conv instantiated)
  show ?thesis using result ordinary by simp
qed

lemma lpp_open_stable_control_model:
  assumes checked: "lpp_open_builtin_check F SP" and reachable: "f\<in>F"
    and outcome: "lpp_stable_source_builtin operation f ts result"
    and control: "(\<exists>a. result=LPPBuiltinCall a) \<or>
      (\<exists>cs ys ns. result=LPPBuiltinBranch cs ys ns) \<or>
      (\<exists>left right. result=LPPBuiltinChoice left right)"
  shows "lpp_inline_return_model SP (lpp_stable_scalar_evaluation operation)
    (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
proof -
  have finite: "lpp_finite_source_builtin f ts result"
    by (rule lpp_stable_source_refines_finite[OF outcome])
  have selected: "(f,length ts)\<in>lpp_builtin_signature"
    by (rule lpp_finite_source_selected[OF finite])
  have excluded: "\<not>lpp_finite_source_builtin ''2:is'' ts result"
    "\<not>lpp_finite_source_builtin ''1:integer'' ts result"
    "\<not>lpp_finite_source_builtin ''2:length'' ts result"
    using control by (auto simp: lpp_finite_source_builtin_def lpp_finite_is_outcome_def lpp_integer_is_outcome_def
      lpp_finite_length_outcome_def lpp_integer_test_outcome_def lpp_integer_source_no_call lpp_integer_source_no_branch lpp_integer_source_no_choice
      simp del: lpp_integer_source_builtin.simps split: option.splits if_splits)
  have ordinary: "f\<noteq>''2:is''" "f\<noteq>''1:integer''" "f\<noteq>''2:length''"
    using finite excluded by auto
  have clause: "((f,lpp_return_builtin_args (length ts)),[],[])\<in>set SP"
    using checked selected reachable ordinary by (auto simp: lpp_open_builtin_check_def)
  let ?us = "map (\<lambda>t. lp_isubst t sigma) ts"
  let ?eta = "\<lambda>v. ?us!(length v-1)"
  have success: "lpp_guarded_success SP (lpp_stable_scalar_evaluation operation)
    (lpp_success_atom_eval (f,lpp_return_builtin_args (length ts)) ?eta)"
    by (rule lpp_guarded_success.clause[OF clause]) simp_all
  have instantiated: "map (\<lambda>t. lp_ieval t ?eta) (lpp_return_builtin_args (length ts))=?us"
    using lpp_return_builtin_args_eval[of ?us] by simp
  have result: "lpp_guarded_success SP (lpp_stable_scalar_evaluation operation) (f,?us)"
    using success by (simp only: lpp_success_atom_eval_def fst_conv snd_conv instantiated)
  show ?thesis using result ordinary by simp
qed

ML \<open>
val checked = [@{thm lpp_open_stable_builtin_model},@{thm lpp_open_stable_probe_model}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted open return builtins" else ();
\<close>
end
