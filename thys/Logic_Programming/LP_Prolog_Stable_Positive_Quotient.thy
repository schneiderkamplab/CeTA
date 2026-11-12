theory LP_Prolog_Stable_Positive_Quotient
 imports LP_Prolog_Stable_Quotient_Descent LP_Prolog_Stable_Context
begin

text \<open>A strictly positive numerator and divisor do not alone imply a
positive truncated quotient. The successful divisibility test is essential.
These premises concern actual evaluations, including compound arithmetic
expressions; they do not type the unevaluated operands as integer literals.\<close>

lemma lpp_stable_exact_positive_quotient:
  assumes compatible: "lpp_stable_integer_operations operation"
    and evaluated: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_2f2f'') [a,b]) result"
    and numerator: "lpp_stable_compare_outcome operation LPPIntLess
      (lpp_integer_value 0) a (LPPBuiltinSuccess LPIVar)"
    and denominator: "lpp_stable_compare_outcome operation LPPIntLess
      (lpp_integer_value 0) b (LPPBuiltinSuccess LPIVar)"
    and exact: "lpp_stable_compare_outcome operation LPPIntEqual a
      (LPIFun (LPCUser ''2:prolog_data_2a'') [result,b]) (LPPBuiltinSuccess LPIVar)"
  shows "\<exists>q. result=lpp_integer_value q \<and> 0<q"
proof -
  obtain n d where left: "lpp_stable_scalar_evaluation operation a (lpp_integer_value n)"
    and right: "lpp_stable_scalar_evaluation operation b (lpp_integer_value d)"
    and result: "result=lpp_integer_value (lpp_trunc_div n d)"
    by (rule lpp_stable_quotient_operands[OF compatible evaluated]) blast
  let ?q = "lpp_trunc_div n d"
  have n: "0<n"
    using lpp_stable_evaluated_integer_comparison[OF lpp_stable_integer_literal left numerator] by simp
  have d: "0<d"
    using lpp_stable_evaluated_integer_comparison[OF lpp_stable_integer_literal right denominator] by simp
  have multiplication: "operation (LPCUser ''2:prolog_data_2a'')
      [lpp_integer_value ?q,lpp_integer_value d]=Some (lpp_integer_value (?q*d))"
    using compatible by (simp add: lpp_stable_integer_operations_def)
  have product: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_2a'') [result,b]) (lpp_integer_value (?q*d))"
    unfolding result
    by (rule lpp_stable_scalar_evaluation.binary[OF lpp_stable_integer_literal
      right multiplication lpp_integer_scalar_observation])
  have equality: "n=?q*d"
    using lpp_stable_evaluated_integer_comparison[OF left product exact] by simp
  have positive_product: "0 < ?q*d" using n equality by simp
  have "0 < ?q"
  proof (rule ccontr)
    assume "\<not>0 < ?q"
    then have nonpositive: "?q\<le>0" by simp
    have "?q*d\<le>0" by (rule mult_nonpos_nonneg[OF nonpositive]) (use d in simp)
    with positive_product show False by simp
  qed
  then show ?thesis using result by blast
qed

lemma lpp_stable_positive_quotient_observation:
  assumes compatible: "lpp_stable_integer_operations operation"
    and evaluated: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_2f2f'') [a,b]) result"
    and numerator: "lpp_stable_compare_outcome operation LPPIntLess
      (lpp_integer_value 0) a (LPPBuiltinSuccess LPIVar)"
    and denominator: "lpp_stable_compare_outcome operation LPPIntLess
      (lpp_integer_value 0) b (LPPBuiltinSuccess LPIVar)"
    and exact: "lpp_stable_compare_outcome operation LPPIntEqual a
      (LPIFun (LPCUser ''2:prolog_data_2a'') [result,b]) (LPPBuiltinSuccess LPIVar)"
  shows "lpp_stable_compare_outcome operation LPPIntLess
    (lpp_integer_value 0) result (LPPBuiltinSuccess LPIVar)"
proof -
  obtain q where result: "result=lpp_integer_value q" and positive: "0<q"
    using lpp_stable_exact_positive_quotient[OF compatible evaluated numerator denominator exact] by blast
  show ?thesis unfolding result
    by (simp add: lpp_stable_compare_integer_exact[OF compatible lpp_integer_evaluation.literal lpp_integer_evaluation.literal]
      lpp_integer_compare_outcome_exact[OF lpp_integer_evaluation.literal lpp_integer_evaluation.literal] positive)
qed

lemma lpp_positive_inputs_do_not_suffice:
  "0<(1::int) \<and> 0<(2::int) \<and> lpp_trunc_div 1 2=0"
  by (simp add: lpp_trunc_div_def)

ML \<open>
val checked = [@{thm lpp_stable_exact_positive_quotient},
  @{thm lpp_stable_positive_quotient_observation}, @{thm lpp_positive_inputs_do_not_suffice}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted positive quotient dependency" else ();
\<close>
end
