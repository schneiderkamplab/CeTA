theory LP_Prolog_Stable_Quotient_Descent
 imports LP_Prolog_Stable_Quotient
begin

lemma lpp_stable_quotient_operands:
  assumes compatible: "lpp_stable_integer_operations operation"
    and evaluated: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_2f2f'') [a,b]) result"
  obtains n d where "lpp_stable_scalar_evaluation operation a (lpp_integer_value n)"
    "lpp_stable_scalar_evaluation operation b (lpp_integer_value d)"
    "d\<noteq>0" "result=lpp_integer_value (lpp_trunc_div n d)"
proof -
  obtain x y where left: "lpp_stable_scalar_evaluation operation a x"
    and right: "lpp_stable_scalar_evaluation operation b y"
    and step: "operation (LPCUser ''2:prolog_data_2f2f'') [x,y]=Some result"
    using evaluated by (cases rule: lpp_stable_scalar_evaluation.cases)
      (auto dest: lpp_scalar_fraction_nullary)
  have contract: "\<forall>a b v. operation (LPCUser ''2:prolog_data_2f2f'') [a,b]=Some v \<longrightarrow>
    (\<exists>n d. a=lpp_integer_value n \<and> b=lpp_integer_value d \<and> d\<noteq>0 \<and>
      v=lpp_integer_value (lpp_trunc_div n d))"
    using compatible by (simp add: lpp_stable_integer_operations_def lpp_stable_quotient_operation_def)
  obtain n d where x: "x=lpp_integer_value n" and y: "y=lpp_integer_value d"
    and nz: "d\<noteq>0" and result: "result=lpp_integer_value (lpp_trunc_div n d)"
    using contract[rule_format, of x y result, OF step] by blast
  show thesis by (rule that[OF left[unfolded x] right[unfolded y] nz result])
qed

lemma lpp_stable_evaluated_integer_comparison:
  assumes left: "lpp_stable_scalar_evaluation operation a (lpp_integer_value n)"
    and right: "lpp_stable_scalar_evaluation operation b (lpp_integer_value m)"
    and success: "lpp_stable_compare_outcome operation c a b (LPPBuiltinSuccess LPIVar)"
  shows "lpp_integer_compare c n m"
  using lpp_stable_compare_values_exact[OF left right lpp_integer_scalar_observation
    lpp_integer_scalar_observation, where comparison=c] success
  by (auto simp: lpp_stable_compare_outcome_def split: if_splits)

text \<open>Strict descent follows from actual successful evaluation and its
actual path guards. The input terms may be compound arithmetic expressions;
no literal-integer assumption is exported to an alternative or caller.\<close>
lemma lpp_stable_quotient_progress:
  assumes compatible: "lpp_stable_integer_operations operation"
    and evaluated: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_2f2f'') [a,b]) result"
    and denominator: "lpp_stable_compare_outcome operation LPPIntLess (lpp_integer_value 1) b
      (LPPBuiltinSuccess LPIVar)"
    and numerator: "lpp_stable_compare_outcome operation LPPIntLess (lpp_integer_value 0) a (LPPBuiltinSuccess LPIVar) \<or>
      lpp_stable_compare_outcome operation LPPIntLessEqual b a (LPPBuiltinSuccess LPIVar) \<or>
      lpp_stable_compare_outcome operation LPPIntLess b a (LPPBuiltinSuccess LPIVar)"
  shows "0\<le>lpp_stable_expression_bound operation result \<and>
    lpp_stable_expression_bound operation result < lpp_stable_expression_bound operation a"
proof -
  obtain n d where left: "lpp_stable_scalar_evaluation operation a (lpp_integer_value n)"
    and right: "lpp_stable_scalar_evaluation operation b (lpp_integer_value d)"
    and result: "result=lpp_integer_value (lpp_trunc_div n d)"
    by (rule lpp_stable_quotient_operands[OF compatible evaluated]) blast
  have d: "1<d"
    using lpp_stable_evaluated_integer_comparison[OF lpp_stable_integer_literal right denominator] by simp
  have n: "0<n" using numerator d
    lpp_stable_evaluated_integer_comparison[OF lpp_stable_integer_literal left, where c=LPPIntLess]
    lpp_stable_evaluated_integer_comparison[OF right left, where c=LPPIntLessEqual]
    lpp_stable_evaluated_integer_comparison[OF right left, where c=LPPIntLess]
    by auto
  have a: "lpp_stable_expression_bound operation a=n"
    by (rule lpp_stable_integer_bound[OF left])
  have q: "lpp_stable_expression_bound operation result=n div d"
    using n d by (simp add: result lpp_stable_integer_bound[OF lpp_stable_integer_literal] lpp_trunc_div_def abs_if)
  show ?thesis using n d int_div_less_self[OF n d]
    by (simp add: a q pos_imp_zdiv_nonneg_iff)
qed

ML \<open>
val checked = [@{thm lpp_stable_quotient_operands}, @{thm lpp_stable_evaluated_integer_comparison},
  @{thm lpp_stable_quotient_progress}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted quotient progress dependency" else ();
\<close>
end
