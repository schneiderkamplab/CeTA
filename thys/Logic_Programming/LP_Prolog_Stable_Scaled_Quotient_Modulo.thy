theory LP_Prolog_Stable_Scaled_Quotient_Modulo
 imports LP_Prolog_Stable_Scaled_Conditions
begin

lemma lpp_scaled_trunc_div_magnitude:
  "lpp_trunc_div n d \<le> abs n"
proof -
  have nonneg: "0\<le>abs n div abs d"
    by (cases "d=0") (auto simp: pos_imp_zdiv_nonneg_iff)
  have bound: "abs n div abs d \<le> abs n"
    by (cases "n=0") (auto intro: int_div_le_self)
  show ?thesis using nonneg bound by (auto simp: lpp_trunc_div_def sgn_if abs_if)
qed

lemma lpp_stable_scaled_quotient_modulo_progress:
  assumes compatible: "lpp_stable_integer_operations operation"
    and evaluated: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_6d6f64'')
        [a,LPIFun (LPCUser ''2:prolog_data_2f2f'') [n,d]]) result"
    and denominator: "lpp_stable_compare_outcome operation LPPIntLess (lpp_integer_value 0)
      (LPIFun (LPCUser ''2:prolog_data_2f2f'') [n,d]) (LPPBuiltinSuccess LPIVar)"
  shows "0\<le>lpp_stable_scaled_bound operation result \<and>
    lpp_stable_scaled_bound operation result < abs (lpp_stable_scaled_bound operation n)"
proof -
  let ?quotient = "LPIFun (LPCUser ''2:prolog_data_2f2f'') [n,d]"
  obtain a0 q where qe: "lpp_stable_scalar_evaluation operation ?quotient (lpp_integer_value q)"
    and result: "result=lpp_integer_value (a0 mod q)"
    by (rule lpp_stable_modulo_operands[OF compatible evaluated]) blast
  obtain n0 d0 where ne: "lpp_stable_scalar_evaluation operation n (lpp_integer_value n0)"
    and q: "q=lpp_trunc_div n0 d0"
    by (rule lpp_stable_quotient_operands[OF compatible qe]) auto
  have positive: "0<q"
    using lpp_stable_evaluated_integer_comparison[OF lpp_stable_integer_literal qe denominator] by simp
  have bounded: "a0 mod q < abs n0"
    using pos_mod_bound[OF positive, of a0] lpp_scaled_trunc_div_magnitude[of n0 d0] q by auto
  have n: "lpp_stable_scaled_bound operation n=n0*lpp_scalar_scale"
    by (rule lpp_stable_scaled_integer[OF ne])
  have r: "lpp_stable_scaled_bound operation result=(a0 mod q)*lpp_scalar_scale"
    by (simp add: result lpp_stable_scaled_integer[OF lpp_stable_integer_literal])
  show ?thesis using positive bounded lpp_scalar_scale_positive
    by (simp add: n r abs_mult pos_mod_sign)
qed

definition lpp_stable_scaled_quotient_modulo_formula where
  "lpp_stable_scaled_quotient_modulo_formula rename n d result =
    (let a=LPPEVariable (rename (LPPScaledKey n));
         r=LPPEVariable (rename (LPPScaledKey result)) in
      Conjunction [Conjunction [lpp_numeric_condition_formula (LPPIntLessEqual,LPPEConstant 0,r),
        Disjunction [lpp_numeric_condition_formula (LPPIntLess,r,a),
          lpp_numeric_condition_formula (LPPIntLess,r,LPPENegate a)]],
        lpp_stable_scaled_modulo_formula rename (Fun (LPCUser ''2:prolog_data_2f2f'') [n,d]) result])"

ML \<open>
val checked = [@{thm lpp_stable_scaled_quotient_modulo_progress}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted compound modulo dependency" else ();
\<close>
end
