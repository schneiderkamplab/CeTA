theory LP_Prolog_Stable_Quotient
 imports LP_Prolog_Stable_Endpoints
begin

text \<open>Successful truncating division fixes its result and both evaluated
operand types. No integer assumption is made about an unevaluated source term.
The operation contract excludes zero divisors and floating operands from success;
the source graph still carries their finite failure/error outcomes.\<close>

lemma lpp_stable_quotient_result:
  assumes compatible: "lpp_stable_integer_operations operation"
    and evaluated: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_2f2f'') [a,lpp_integer_value d]) result"
  obtains n where "lpp_stable_scalar_evaluation operation a (lpp_integer_value n)"
    "d\<noteq>0" "result=lpp_integer_value (lpp_trunc_div n d)"
proof -
  obtain x y where left: "lpp_stable_scalar_evaluation operation a x"
    and right: "lpp_stable_scalar_evaluation operation (lpp_integer_value d) y"
    and step: "operation (LPCUser ''2:prolog_data_2f2f'') [x,y]=Some result"
    using evaluated by (cases rule: lpp_stable_scalar_evaluation.cases)
      (auto dest: lpp_scalar_fraction_nullary)
  have y: "y=lpp_integer_value d"
    by (rule lpp_stable_scalar_evaluation_unique[OF right lpp_stable_integer_literal])
  have contract: "\<forall>a b v. operation (LPCUser ''2:prolog_data_2f2f'') [a,b]=Some v \<longrightarrow>
    (\<exists>n d. a=lpp_integer_value n \<and> b=lpp_integer_value d \<and> d\<noteq>0 \<and>
      v=lpp_integer_value (lpp_trunc_div n d))"
    using compatible by (simp add: lpp_stable_integer_operations_def lpp_stable_quotient_operation_def)
  obtain n m where x: "x=lpp_integer_value n" and m: "y=lpp_integer_value m"
    and nz: "m\<noteq>0" and result: "result=lpp_integer_value (lpp_trunc_div n m)"
    using contract[rule_format, of x y result, OF step] by blast
  have "m=d" using m y by simp
  then show thesis using that left x nz result by blast
qed

lemma lpp_stable_integer_bound:
  assumes evaluated: "lpp_stable_scalar_evaluation operation a (lpp_integer_value n)"
  shows "lpp_stable_expression_bound operation a=n"
  using lpp_stable_expression_bound_exact[OF evaluated]
    lpp_scalar_floor_exact[OF lpp_integer_scalar_observation, of n]
  by simp

lemma lpp_stable_quotient_bounds:
  assumes compatible: "lpp_stable_integer_operations operation"
    and positive: "0<d"
    and evaluated: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_2f2f'') [a,lpp_integer_value d]) result"
  defines "n \<equiv> lpp_stable_expression_bound operation a"
    and "q \<equiv> lpp_stable_expression_bound operation result"
  shows "(0\<le>n \<and> q=n div d) \<or> (n<0 \<and> q= - ((-n) div d))"
proof -
  obtain k where a: "lpp_stable_scalar_evaluation operation a (lpp_integer_value k)"
    and result: "result=lpp_integer_value (lpp_trunc_div k d)"
    by (rule lpp_stable_quotient_result[OF compatible evaluated]) blast
  have n: "n=k" by (simp add: n_def lpp_stable_integer_bound[OF a])
  have q: "q=lpp_trunc_div k d"
    by (simp add: q_def result lpp_stable_integer_bound[OF lpp_stable_integer_literal])
  show ?thesis using positive by (auto simp: n q lpp_trunc_div_def abs_if)
qed

ML \<open>
val checked = [@{thm lpp_stable_quotient_result}, @{thm lpp_stable_integer_bound},
  @{thm lpp_stable_quotient_bounds}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted successful quotient dependency" else ();
\<close>
end
