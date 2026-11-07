theory LP_Prolog_Stable_Modulo
 imports LP_Prolog_Stable_Quotient_Descent
begin

lemma lpp_stable_modulo_operands:
  assumes compatible: "lpp_stable_integer_operations operation"
    and evaluated: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_6d6f64'') [a,b]) result"
  obtains n d where "lpp_stable_scalar_evaluation operation a (lpp_integer_value n)"
    "lpp_stable_scalar_evaluation operation b (lpp_integer_value d)"
    "d\<noteq>0" "result=lpp_integer_value (n mod d)"
proof -
  obtain x y where left: "lpp_stable_scalar_evaluation operation a x"
    and right: "lpp_stable_scalar_evaluation operation b y"
    and step: "operation (LPCUser ''2:prolog_data_6d6f64'') [x,y]=Some result"
    using evaluated by (cases rule: lpp_stable_scalar_evaluation.cases)
      (auto dest: lpp_scalar_fraction_nullary)
  have contract: "\<forall>a b v. operation (LPCUser ''2:prolog_data_6d6f64'') [a,b]=Some v \<longrightarrow>
    (\<exists>n d. a=lpp_integer_value n \<and> b=lpp_integer_value d \<and> d\<noteq>0 \<and>
      v=lpp_integer_value (n mod d))"
    using compatible by (simp add: lpp_stable_integer_operations_def lpp_stable_modulo_operation_def)
  obtain n d where x: "x=lpp_integer_value n" and y: "y=lpp_integer_value d"
    and nz: "d\<noteq>0" and result: "result=lpp_integer_value (n mod d)"
    using contract[rule_format, of x y result, OF step] by blast
  show thesis by (rule that[OF left[unfolded x] right[unfolded y] nz result])
qed

lemma lpp_stable_modulo_progress:
  assumes compatible: "lpp_stable_integer_operations operation"
    and evaluated: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_6d6f64'') [a,b]) result"
    and denominator: "lpp_stable_compare_outcome operation LPPIntLess (lpp_integer_value 0) b
      (LPPBuiltinSuccess LPIVar)"
  shows "0\<le>lpp_stable_expression_bound operation result \<and>
    lpp_stable_expression_bound operation result < lpp_stable_expression_bound operation b"
proof -
  obtain n d where right: "lpp_stable_scalar_evaluation operation b (lpp_integer_value d)"
    and result: "result=lpp_integer_value (n mod d)"
    by (rule lpp_stable_modulo_operands[OF compatible evaluated]) blast
  have d: "0<d"
    using lpp_stable_evaluated_integer_comparison[OF lpp_stable_integer_literal right denominator] by simp
  have b: "lpp_stable_expression_bound operation b=d"
    by (rule lpp_stable_integer_bound[OF right])
  have r: "lpp_stable_expression_bound operation result=n mod d"
    by (simp add: result lpp_stable_integer_bound[OF lpp_stable_integer_literal])
  show ?thesis using d by (simp add: b r pos_mod_sign pos_mod_bound)
qed

ML \<open>
val checked = [@{thm lpp_stable_modulo_operands}, @{thm lpp_stable_modulo_progress}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted modulo progress dependency" else ();
\<close>
end
