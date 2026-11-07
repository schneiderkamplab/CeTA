theory LP_Prolog_Stable_Integer_Compatibility
  imports LP_Prolog_Stable_Scalar_Evaluation
begin

definition lpp_trunc_div :: "int \<Rightarrow> int \<Rightarrow> int" where
  "lpp_trunc_div n d = (if n<0 then -1 else 1) * (if d<0 then -1 else 1) * (abs n div abs d)"

definition lpp_stable_quotient_operation where
  "lpp_stable_quotient_operation operation =
    (\<forall>a b v. operation (LPCUser ''2:prolog_data_2f2f'') [a,b]=Some v \<longrightarrow>
      (\<exists>n d. a=lpp_integer_value n \<and> b=lpp_integer_value d \<and> d\<noteq>0 \<and>
        v=lpp_integer_value (lpp_trunc_div n d)))"

definition lpp_stable_modulo_operation where
  "lpp_stable_modulo_operation operation =
    (\<forall>a b v. operation (LPCUser ''2:prolog_data_6d6f64'') [a,b]=Some v \<longrightarrow>
      (\<exists>n d. a=lpp_integer_value n \<and> b=lpp_integer_value d \<and> d\<noteq>0 \<and>
        v=lpp_integer_value (n mod d)))"

definition lpp_stable_integer_operations where
  "lpp_stable_integer_operations operation =
    (lpp_stable_modulo_operation operation \<and> lpp_stable_quotient_operation operation \<and> (\<forall>n. operation (LPCUser ''1:prolog_data_2b'') [lpp_integer_value n]=Some (lpp_integer_value n)) \<and>
     (\<forall>n. operation (LPCUser ''1:prolog_data_2d'') [lpp_integer_value n]=Some (lpp_integer_value (-n))) \<and>
     (\<forall>n m. operation (LPCUser ''2:prolog_data_2b'') [lpp_integer_value n,lpp_integer_value m]=Some (lpp_integer_value (n+m))) \<and>
     (\<forall>n m. operation (LPCUser ''2:prolog_data_2d'') [lpp_integer_value n,lpp_integer_value m]=Some (lpp_integer_value (n-m))) \<and>
     (\<forall>n m. operation (LPCUser ''2:prolog_data_2a'') [lpp_integer_value n,lpp_integer_value m]=Some (lpp_integer_value (n*m))) \<and>
     (\<forall>n d. d\<noteq>0 \<longrightarrow> operation (LPCUser ''2:prolog_data_646976'') [lpp_integer_value n,lpp_integer_value d]=Some (lpp_integer_value (n div d))) \<and>
     (\<forall>n d. d\<noteq>0 \<longrightarrow> operation (LPCUser ''2:prolog_data_6d6f64'') [lpp_integer_value n,lpp_integer_value d]=Some (lpp_integer_value (n mod d))))"

lemma lpp_integer_scalar_observation:
  "lpp_scalar_fraction (lpp_integer_value n) n 1"
  by (simp add: lpp_scalar_fraction_def)

lemma lpp_stable_integer_literal:
  "lpp_stable_scalar_evaluation operation (lpp_integer_value n) (lpp_integer_value n)"
  by (rule lpp_stable_scalar_evaluation.scalar[OF lpp_integer_scalar_observation])

lemma lpp_integer_evaluation_stable:
  assumes compatible: "lpp_stable_integer_operations operation"
    and evaluated: "lpp_integer_evaluation expression n"
  shows "lpp_stable_scalar_evaluation operation expression (lpp_integer_value n)"
  using evaluated compatible
  by (induction rule: lpp_integer_evaluation.induct)
    (auto simp: lpp_stable_integer_operations_def intro: lpp_stable_scalar_evaluation.intros lpp_integer_scalar_observation lpp_stable_integer_literal)

lemma lpp_stable_evaluation_integer_exact:
  assumes compatible: "lpp_stable_integer_operations operation"
    and evaluated: "lpp_integer_evaluation expression n"
  shows "lpp_stable_scalar_evaluation operation expression v \<longleftrightarrow> v=lpp_integer_value n"
  using lpp_integer_evaluation_stable[OF compatible evaluated]
    lpp_stable_scalar_evaluation_unique by blast

lemma lpp_stable_evaluation_finite_envelope:
  assumes compatible: "lpp_stable_integer_operations operation"
    and evaluated: "lpp_stable_scalar_evaluation operation expression v"
  shows "lpp_finite_evaluation_result expression v"
proof (cases "\<exists>n. lpp_integer_evaluation expression n")
  case True
  then obtain n where integer: "lpp_integer_evaluation expression n" by blast
  have "v=lpp_integer_value n"
    using lpp_stable_evaluation_integer_exact[OF compatible integer] evaluated by blast
  then show ?thesis using integer
    by (auto simp: lpp_finite_evaluation_result_def lpp_integer_result_def)
next
  case False
  have ground: "lp_seg_ground expression"
    using lpp_stable_scalar_evaluation_ground[OF evaluated] by blast
  obtain n d where "lpp_scalar_fraction v n d"
    using lpp_stable_scalar_evaluation_result[OF evaluated] by blast
  then have "\<exists>f. v=LPIFun (LPCUser f) []" by (rule lpp_scalar_fraction_nullary)
  then show ?thesis using False ground by (simp add: lpp_finite_evaluation_result_def)
qed

lemma lpp_stable_evaluation_integer_contract:
  assumes compatible: "lpp_stable_integer_operations operation"
  shows "lpp_eval_integer_contract TYPE('v) (lpp_stable_scalar_evaluation operation)"
proof (unfold lpp_eval_integer_contract_def, intro allI impI)
  fix K :: "'v list" and expression eta v
  assume checked: "lpp_expression_check K expression" and known: "lpp_integer_known K eta"
    and returned: "lpp_stable_scalar_evaluation operation (lp_ieval (lpp_expression_term expression) eta) v"
  obtain n where integer: "lpp_integer_evaluation (lp_ieval (lpp_expression_term expression) eta) n"
    using lpp_checked_expression_finishes[OF checked known] by blast
  have "v=lpp_integer_value n"
    using lpp_stable_evaluation_integer_exact[OF compatible integer] returned by blast
  then show "lpp_is_integer v" by (auto simp: lpp_is_integer_def)
qed

ML \<open>
val checked = [@{thm lpp_integer_evaluation_stable},
  @{thm lpp_stable_evaluation_integer_exact}, @{thm lpp_stable_evaluation_finite_envelope},
  @{thm lpp_stable_evaluation_integer_contract}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable integer compatibility dependency" else ();
\<close>
end
