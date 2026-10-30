theory LP_Prolog_Arithmetic_Semantics
  imports LP_Prolog_Integer_Encoding LP_Prolog_Success_Types
begin

text \<open>Integer evaluation has a unique result, including on rational runtime
terms: a successful integer derivation only traverses a finite arithmetic tree.
The injective source alphabet keeps distinct integers and quoted atoms apart.\<close>

lemma lpp_integer_divide_invert:
  "lpp_integer_evaluation (LPIFun (LPCUser ''2:prolog_data_646976'') [a,lpp_integer_value d]) m \<Longrightarrow>
   \<exists>v. lpp_integer_evaluation a v \<and> m=v div d"
  by (erule lpp_integer_evaluation.cases) (auto simp: lpp_integer_value_def)

lemma lpp_integer_modulo_invert:
  "lpp_integer_evaluation (LPIFun (LPCUser ''2:prolog_data_6d6f64'') [a,lpp_integer_value d]) m \<Longrightarrow>
   \<exists>v. lpp_integer_evaluation a v \<and> m=v mod d"
  by (erule lpp_integer_evaluation.cases) (auto simp: lpp_integer_value_def)

theorem lpp_integer_evaluation_unique:
  assumes first: "lpp_integer_evaluation a n"
    and second: "lpp_integer_evaluation a m"
  shows "n=m"
  using first second
proof (induction arbitrary: m rule: lpp_integer_evaluation.induct)
  case (literal n)
  from literal.prems show ?case
    by (cases rule: lpp_integer_evaluation.cases)
      (auto simp: lpp_integer_value_def)
next
  case (positive a n)
  obtain v where ev: "lpp_integer_evaluation a v" and result: "m=v"
    using positive.prems by (cases rule: lpp_integer_evaluation.cases)
      (auto simp: lpp_integer_value_def)
  have "n=v" by (rule positive.IH[OF ev])
  then show ?case using result by simp
next
  case (negate a n)
  obtain v where ev: "lpp_integer_evaluation a v" and result: "m=-v"
    using negate.prems by (cases rule: lpp_integer_evaluation.cases)
      (auto simp: lpp_integer_value_def)
  have "n=v" by (rule negate.IH[OF ev])
  then show ?case using result by simp
next
  case (add a n b k)
  obtain v w where left: "lpp_integer_evaluation a v" and right: "lpp_integer_evaluation b w"
    and result: "m=v+w"
    using add.prems by (cases rule: lpp_integer_evaluation.cases)
      (auto simp: lpp_integer_value_def)
  have nv: "n=v" by (rule add.IH(1)[OF left])
  have kw: "k=w" by (rule add.IH(2)[OF right])
  show ?case using nv kw result by simp
next
  case (subtract a n b k)
  obtain v w where left: "lpp_integer_evaluation a v" and right: "lpp_integer_evaluation b w"
    and result: "m=v-w"
    using subtract.prems by (cases rule: lpp_integer_evaluation.cases)
      (auto simp: lpp_integer_value_def)
  have nv: "n=v" by (rule subtract.IH(1)[OF left])
  have kw: "k=w" by (rule subtract.IH(2)[OF right])
  show ?case using nv kw result by simp
next
  case (multiply a n b k)
  obtain v w where left: "lpp_integer_evaluation a v" and right: "lpp_integer_evaluation b w"
    and result: "m = v * w"
    using multiply.prems by (cases rule: lpp_integer_evaluation.cases)
      (auto simp: lpp_integer_value_def)
  have nv: "n=v" by (rule multiply.IH(1)[OF left])
  have kw: "k=w" by (rule multiply.IH(2)[OF right])
  have product: "n * k = v * w" by (rule arg_cong2[OF nv kw])
  show ?case by (rule HOL.trans[OF product result[symmetric]])
next
  case (divide a n d)
  obtain v where ev: "lpp_integer_evaluation a v" and result: "m=v div d"
    using lpp_integer_divide_invert[OF divide.prems] by blast
  have eq: "n=v" by (rule divide.IH[OF ev])
  have evaluated: "n div d=v div d" by (rule arg_cong[OF eq])
  show ?case by (rule HOL.trans[OF evaluated result[symmetric]])

next
  case (modulo a n d)
  obtain v where ev: "lpp_integer_evaluation a v" and result: "m=v mod d"
    using lpp_integer_modulo_invert[OF modulo.prems] by blast
  have eq: "n=v" by (rule modulo.IH[OF ev])
  have evaluated: "n mod d=v mod d" by (rule arg_cong[OF eq])
  show ?case by (rule HOL.trans[OF evaluated result[symmetric]])

qed

definition lpp_integer_result where
  "lpp_integer_result e t = (\<exists>n. lpp_integer_evaluation e n \<and> t=lpp_integer_value n)"

lemma lpp_integer_result_contract:
  "lpp_eval_integer_contract TYPE('v) lpp_integer_result"
  by (auto simp: lpp_eval_integer_contract_def lpp_integer_result_def lpp_is_integer_def)

theorem lpp_integer_result_exact:
  assumes checked: "lpp_expression_check K e"
    and typed: "\<And>x. x\<in>set K \<Longrightarrow> eta x=lpp_integer_value (rho x)"
  shows "lpp_integer_result (lp_ieval (lpp_expression_term e) eta) t \<longleftrightarrow>
    t=lpp_integer_value (lpp_expression_value e rho)"
proof -
  have evaluated: "lpp_integer_evaluation (lp_ieval (lpp_expression_term e) eta) (lpp_expression_value e rho)"
    by (rule lpp_expression_evaluation[OF checked typed])
  show ?thesis using evaluated lpp_integer_evaluation_unique
    by (auto simp: lpp_integer_result_def)
qed

corollary lpp_integer_success_contract:
  "lpp_check_success_program S P proofs \<Longrightarrow> lpp_guarded_success P lpp_integer_result a \<Longrightarrow>
    lpp_success_summary_holds S a"
  by (rule lpp_check_success_program_sound[OF _ lpp_integer_result_contract])

end
