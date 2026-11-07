theory LP_Prolog_Stable_Magnitude_Algebra
 imports LP_Prolog_Stable_Magnitude_Conditions
begin

text \<open>Universal magnitude bounds preserve failed evaluations as zero
observations. They do not assume that ground arguments are integers.\<close>

lemma lpp_stable_scaled_evaluation_value:
  assumes evaluation: "lpp_stable_scalar_evaluation operation expression result"
  shows "lpp_stable_scaled_bound operation expression = lpp_stable_scaled_bound operation result"
proof -
  obtain n d where scalar: "lpp_scalar_fraction result n d"
    using lpp_stable_scalar_evaluation_result[OF evaluation] by blast
  have literal: "lpp_stable_scalar_evaluation operation result result"
    by (rule lpp_stable_scalar_evaluation.scalar[OF scalar])
  show ?thesis by (simp only: lpp_stable_scaled_bound_exact[OF evaluation]
    lpp_stable_scaled_bound_exact[OF literal])
qed

lemma lpp_trunc_div_abs_bound:
  "abs (lpp_trunc_div n d) \<le> abs n"
proof -
  have nonneg: "0\<le>abs n div abs d"
    by (cases "d=0") (auto simp: pos_imp_zdiv_nonneg_iff)
  have bound: "abs n div abs d \<le> abs n"
    by (cases "n=0") (auto intro: int_div_le_self)
  show ?thesis using nonneg bound
    by (auto simp: lpp_trunc_div_def sgn_if abs_if)
qed

lemma lpp_stable_quotient_abs_bound:
  assumes compatible: "lpp_stable_integer_operations operation"
  shows "abs (lpp_stable_scaled_bound operation
    (LPIFun (LPCUser ''2:prolog_data_2f2f'') [a,b])) \<le>
    abs (lpp_stable_scaled_bound operation a)"
proof (cases "\<exists>v. lpp_stable_scalar_evaluation operation
    (LPIFun (LPCUser ''2:prolog_data_2f2f'') [a,b]) v")
  case False then show ?thesis by (simp add: lpp_stable_scaled_bound_def)
next
  case True
  then obtain v where evaluated: "lpp_stable_scalar_evaluation operation
    (LPIFun (LPCUser ''2:prolog_data_2f2f'') [a,b]) v" by blast
  obtain n d where numerator: "lpp_stable_scalar_evaluation operation a (lpp_integer_value n)"
    and result: "v=lpp_integer_value (lpp_trunc_div n d)"
    by (rule lpp_stable_quotient_operands[OF compatible evaluated]) blast
  have q: "lpp_stable_scaled_bound operation
      (LPIFun (LPCUser ''2:prolog_data_2f2f'') [a,b]) = lpp_trunc_div n d*lpp_scalar_scale"
    by (rule lpp_stable_scaled_integer[OF evaluated[unfolded result]])
  have n: "lpp_stable_scaled_bound operation a=n*lpp_scalar_scale"
    by (rule lpp_stable_scaled_integer[OF numerator])
  show ?thesis using lpp_trunc_div_abs_bound[of n d] lpp_scalar_scale_positive
    by (simp add: q n abs_mult)
qed

lemma lpp_stable_modulo_abs_bound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and evaluated: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_6d6f64'') [a,b]) result"
  shows "abs (lpp_stable_scaled_bound operation result) \<le>
    abs (lpp_stable_scaled_bound operation b)"
proof -
  obtain n d where denominator: "lpp_stable_scalar_evaluation operation b (lpp_integer_value d)"
    and nz: "d\<noteq>0" and result: "result=lpp_integer_value (n mod d)"
    by (rule lpp_stable_modulo_operands[OF compatible evaluated]) blast
  have r: "lpp_stable_scaled_bound operation result=(n mod d)*lpp_scalar_scale"
    by (simp add: result lpp_stable_scaled_integer[OF lpp_stable_integer_literal])
  have d: "lpp_stable_scaled_bound operation b=d*lpp_scalar_scale"
    by (rule lpp_stable_scaled_integer[OF denominator])
  show ?thesis using abs_mod_less[OF nz, of n] lpp_scalar_scale_positive
    by (simp add: r d abs_mult)
qed

ML \<open>
val checked = [@{thm lpp_stable_scaled_evaluation_value},
  @{thm lpp_stable_quotient_abs_bound}, @{thm lpp_stable_modulo_abs_bound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted magnitude algebra dependency" else ();
\<close>
end
