theory LP_Prolog_Source_Return_Builtins
 imports LP_Prolog_Source_Return_Model LP_Prolog_Probe_Return_Domain
begin

text \<open>The return model includes every successful builtin outcome. Only
integer evaluation and the integer test add type information; other operations
contribute unrestricted successful facts. Domain coverage remains a separate
source-graph obligation.\<close>

definition lpp_return_builtin_args :: "nat \<Rightarrow> (string lp_cut_symbol,string) term list" where
  "lpp_return_builtin_args n = map (\<lambda>i. Var (replicate (Suc i) CHR ''x'')) [0..<n]"

definition lpp_return_builtin_guards :: "string \<Rightarrow> string lpp_success_guard list" where
  "lpp_return_builtin_guards f =
    (if f=''2:is'' then [LPPSEvaluates (Var ''xx'') (Var ''x''),LPPSInteger (Var ''x'')]
     else if f=''1:integer'' then [LPPSInteger (Var ''x'')] else [])"

definition lpp_return_builtin_clause :: "string \<Rightarrow> nat \<Rightarrow> string lpp_success_clause" where
  "lpp_return_builtin_clause f n = ((f,lpp_return_builtin_args n),[],lpp_return_builtin_guards f)"

definition lpp_return_builtin_check where
  "lpp_return_builtin_check F SP = (\<forall>(f,n)\<in>lpp_builtin_signature.
    f\<in>F \<longrightarrow> lpp_return_builtin_clause f n\<in>set SP)"

lemma lpp_return_builtin_args_eval:
  "map (\<lambda>t. lp_ieval t (\<lambda>v. ts!(length v-1))) (lpp_return_builtin_args (length ts)) = ts"
  by (rule nth_equalityI) (auto simp: lpp_return_builtin_args_def)

lemma lpp_return_builtin_is_guards:
  assumes outcome: "lpp_integer_source_builtin ''2:is'' ts (LPPBuiltinSuccess sigma)"
  shows "list_all (lpp_success_guard_holds lpp_integer_result (\<lambda>v. (map (\<lambda>t. lp_isubst t sigma) ts)!(length v-1)))
    (lpp_return_builtin_guards ''2:is'')"
proof -
  have length: "length ts=2" and success: "lpp_integer_is_outcome (ts!0) (ts!1) (LPPBuiltinSuccess sigma)"
    using outcome by simp_all
  have result: "lpp_integer_result (ts!1) (lp_isubst (ts!0) sigma)" and fixed: "lp_isubst (ts!1) sigma=ts!1"
    using lpp_integer_is_success_evidence[OF success] by auto
  show ?thesis using result fixed by (auto simp: lpp_return_builtin_guards_def length lpp_integer_result_def lpp_is_integer_def)
qed

lemma lpp_return_builtin_integer_guards:
  assumes outcome: "lpp_integer_source_builtin ''1:integer'' ts (LPPBuiltinSuccess sigma)"
  shows "list_all (lpp_success_guard_holds lpp_integer_result (\<lambda>v. (map (\<lambda>t. lp_isubst t sigma) ts)!(length v-1)))
    (lpp_return_builtin_guards ''1:integer'')"
  using outcome by (auto simp: lpp_return_builtin_guards_def lpp_integer_test_outcome_def split: if_splits)

theorem lpp_return_builtin_model:
  assumes checked: "lpp_return_builtin_check F SP"
    and reachable: "f\<in>F"
    and outcome: "lpp_integer_source_builtin f ts (LPPBuiltinSuccess sigma)"
  shows "lpp_source_return_model SP (lp_isubst (LPIFun (LPCUser f) ts) sigma)"
proof -
  let ?us = "map (\<lambda>t. lp_isubst t sigma) ts"
  let ?eta = "\<lambda>v. ?us!(length v-1)"
  have selected: "(f,length ts)\<in>lpp_builtin_signature"
    by (rule lpp_integer_source_selected[OF outcome])
  have clause: "((f,lpp_return_builtin_args (length ts)),[],lpp_return_builtin_guards f)\<in>set SP"
    using checked selected reachable by (auto simp: lpp_return_builtin_check_def lpp_return_builtin_clause_def)
  have guards: "list_all (lpp_success_guard_holds lpp_integer_result ?eta) (lpp_return_builtin_guards f)"
  proof (cases "f=''2:is''")
    case True
    have op: "lpp_integer_source_builtin ''2:is'' ts (LPPBuiltinSuccess sigma)"
      using outcome True by simp
    show ?thesis using lpp_return_builtin_is_guards[OF op] by (simp only: True)
  next
    case no_is: False
    show ?thesis
    proof (cases "f=''1:integer''")
      case True
      have op: "lpp_integer_source_builtin ''1:integer'' ts (LPPBuiltinSuccess sigma)"
        using outcome True by simp
      show ?thesis using lpp_return_builtin_integer_guards[OF op] by (simp only: True)
    next
      case False
      show ?thesis by (simp add: lpp_return_builtin_guards_def no_is False)
    qed
  qed
  have success: "lpp_guarded_success SP lpp_integer_result
    (lpp_success_atom_eval (f,lpp_return_builtin_args (length ts)) ?eta)"
    by (rule lpp_guarded_success.clause[OF clause guards]) simp
  have instantiated: "map (\<lambda>t. lp_ieval t ?eta) (lpp_return_builtin_args (length ts))=?us"
    using lpp_return_builtin_args_eval[of ?us] by simp
  have result: "lpp_guarded_success SP lpp_integer_result (f,?us)"
    using success by (simp only: lpp_success_atom_eval_def fst_conv snd_conv instantiated)
  show ?thesis using result by simp
qed

end
