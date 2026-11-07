theory LP_Prolog_Stable_Magnitude_Quotient_Descent
 imports LP_Prolog_Stable_Magnitude_Algebra
begin

lemma lpp_trunc_div_abs_strict:
  assumes divisor: "1<abs d" and numerator: "0<abs n"
  shows "abs (lpp_trunc_div n d)<abs n"
proof -
  have nonneg: "0\<le>abs n div abs d"
    by (cases "d=0") (auto simp: pos_imp_zdiv_nonneg_iff)
  have strict_bound: "abs n div abs d<abs n"
    by (rule int_div_less_self[OF numerator divisor])
  show ?thesis using nonneg strict_bound
    by (auto simp: lpp_trunc_div_def sgn_if abs_if)
qed

lemma lpp_stable_quotient_abs_strict:
  assumes compatible: "lpp_stable_integer_operations operation"
    and divisor: "lpp_scalar_scale<abs (lpp_stable_scaled_bound operation b)"
    and numerator: "0<abs (lpp_stable_scaled_bound operation a)"
  shows "abs (lpp_stable_scaled_bound operation
    (LPIFun (LPCUser ''2:prolog_data_2f2f'') [a,b])) <
    abs (lpp_stable_scaled_bound operation a)"
proof (cases "\<exists>v. lpp_stable_scalar_evaluation operation
    (LPIFun (LPCUser ''2:prolog_data_2f2f'') [a,b]) v")
  case False then show ?thesis using numerator by (simp add: lpp_stable_scaled_bound_def)
next
  case True
  then obtain v where evaluated: "lpp_stable_scalar_evaluation operation
    (LPIFun (LPCUser ''2:prolog_data_2f2f'') [a,b]) v" by blast
  obtain n d where ne: "lpp_stable_scalar_evaluation operation a (lpp_integer_value n)"
    and de: "lpp_stable_scalar_evaluation operation b (lpp_integer_value d)"
    and result: "v=lpp_integer_value (lpp_trunc_div n d)"
    by (rule lpp_stable_quotient_operands[OF compatible evaluated]) blast
  have q: "lpp_stable_scaled_bound operation
      (LPIFun (LPCUser ''2:prolog_data_2f2f'') [a,b])=lpp_trunc_div n d*lpp_scalar_scale"
    by (rule lpp_stable_scaled_integer[OF evaluated[unfolded result]])
  have n: "lpp_stable_scaled_bound operation a=n*lpp_scalar_scale"
    and d: "lpp_stable_scaled_bound operation b=d*lpp_scalar_scale"
    using lpp_stable_scaled_integer[OF ne] lpp_stable_scaled_integer[OF de] by auto
  have nd: "0<abs n" "1<abs d"
    using numerator divisor lpp_scalar_scale_positive by (auto simp: n d abs_mult)
  show ?thesis using lpp_trunc_div_abs_strict[OF nd(2) nd(1)] lpp_scalar_scale_positive
    by (simp add: q n abs_mult)
qed

ML \<open>
val checked = [@{thm lpp_stable_quotient_abs_strict}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted strict magnitude quotient dependency" else ();
\<close>
end
