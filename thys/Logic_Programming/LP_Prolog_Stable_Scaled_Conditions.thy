theory LP_Prolog_Stable_Scaled_Conditions
 imports LP_Prolog_Stable_Modulo
begin

lemma lpp_stable_scaled_integer:
  "lpp_stable_scalar_evaluation operation t (lpp_integer_value n) \<Longrightarrow>
    lpp_stable_scaled_bound operation t=n*lpp_scalar_scale"
  using lpp_scalar_scaled_exact[OF lpp_integer_scalar_observation, of n]
  by (simp add: lpp_stable_scaled_bound_exact)

definition lpp_scaled_expression where
  "lpp_scaled_expression t = (if t=lpp_integer_term 0 then LPPEConstant 0
    else LPPEVariable (LPPScaledKey t))"

lemma lpp_scaled_expression_value:
  "lpp_expression_value (lpp_scaled_expression t) (lpp_stable_key_value operation eta rho) =
    lpp_stable_scaled_bound operation (lp_ieval t eta)"
  by (auto simp: lpp_scaled_expression_def lpp_stable_scaled_integer[OF lpp_stable_integer_literal])

lemma lpp_stable_scaled_modulo_progress:
  assumes compatible: "lpp_stable_integer_operations operation"
    and evaluated: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_6d6f64'') [a,b]) result"
    and denominator: "lpp_stable_compare_outcome operation LPPIntLess (lpp_integer_value 0) b
      (LPPBuiltinSuccess LPIVar)"
  shows "0\<le>lpp_stable_scaled_bound operation result \<and>
    lpp_stable_scaled_bound operation result < lpp_stable_scaled_bound operation b"
proof -
  obtain n d where right: "lpp_stable_scalar_evaluation operation b (lpp_integer_value d)"
    and result: "result=lpp_integer_value (n mod d)"
    by (rule lpp_stable_modulo_operands[OF compatible evaluated]) blast
  have d: "0<d"
    using lpp_stable_evaluated_integer_comparison[OF lpp_stable_integer_literal right denominator] by simp
  have b: "lpp_stable_scaled_bound operation b=d*lpp_scalar_scale"
    by (rule lpp_stable_scaled_integer[OF right])
  have r: "lpp_stable_scaled_bound operation result=(n mod d)*lpp_scalar_scale"
    by (simp add: result lpp_stable_scaled_integer[OF lpp_stable_integer_literal])
  show ?thesis using d lpp_scalar_scale_positive
    by (simp add: b r pos_mod_sign pos_mod_bound)
qed

definition lpp_stable_scaled_modulo_formula where
  "lpp_stable_scaled_modulo_formula rename b result =
    (let n=LPPEVariable (rename (LPPScaledKey b));
         r=LPPEVariable (rename (LPPScaledKey result)) in
      Conjunction [lpp_numeric_condition_formula (LPPIntLessEqual,LPPEConstant 0,r),
        lpp_numeric_condition_formula (LPPIntLess,r,n)])"

ML \<open>
val checked = [@{thm lpp_stable_scaled_integer}, @{thm lpp_scaled_expression_value},
  @{thm lpp_stable_scaled_modulo_progress}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted scaled condition dependency" else ();
\<close>
end
