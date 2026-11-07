theory LP_Prolog_Stable_Magnitude_Conditions
 imports LP_Prolog_Stable_Scaled_Quotient_Modulo
begin

definition lpp_magnitude_expression where
  "lpp_magnitude_expression t = (if t=lpp_integer_term 0 then LPPEConstant 0
    else LPPEVariable (LPPMagnitudeKey t))"

lemma lpp_magnitude_expression_value:
  "lpp_expression_value (lpp_magnitude_expression t) (lpp_stable_key_value operation eta rho) =
    abs (lpp_stable_scaled_bound operation (lp_ieval t eta))"
  by (auto simp: lpp_magnitude_expression_def lpp_stable_scaled_integer[OF lpp_stable_integer_literal])

lemma lpp_stable_magnitude_order:
  assumes observed: "lpp_stable_compare_outcome operation (if is_strict then LPPIntLess else LPPIntLessEqual)
    a b (LPPBuiltinSuccess LPIVar)"
    and nonnegative: "0\<le>lpp_stable_scaled_bound operation a"
  shows "lpp_integer_compare (if is_strict then LPPIntLess else LPPIntLessEqual)
    (abs (lpp_stable_scaled_bound operation a)) (abs (lpp_stable_scaled_bound operation b))"
  using lpp_stable_scaled_comparison[OF observed] nonnegative
  by (cases is_strict) auto

lemma lpp_stable_magnitude_modulo_progress:
  assumes compatible: "lpp_stable_integer_operations operation"
    and evaluated: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_6d6f64'') [a,b]) result"
    and denominator: "lpp_stable_compare_outcome operation LPPIntLess (lpp_integer_value 0) b
      (LPPBuiltinSuccess LPIVar)"
  shows "0\<le>abs (lpp_stable_scaled_bound operation result) \<and>
    abs (lpp_stable_scaled_bound operation result) < abs (lpp_stable_scaled_bound operation b)"
  using lpp_stable_scaled_modulo_progress[OF compatible evaluated denominator] by auto

lemma lpp_stable_magnitude_quotient_modulo_progress:
  assumes compatible: "lpp_stable_integer_operations operation"
    and evaluated: "lpp_stable_scalar_evaluation operation
      (LPIFun (LPCUser ''2:prolog_data_6d6f64'')
        [a,LPIFun (LPCUser ''2:prolog_data_2f2f'') [n,d]]) result"
    and denominator: "lpp_stable_compare_outcome operation LPPIntLess (lpp_integer_value 0)
      (LPIFun (LPCUser ''2:prolog_data_2f2f'') [n,d]) (LPPBuiltinSuccess LPIVar)"
  shows "0\<le>abs (lpp_stable_scaled_bound operation result) \<and>
    abs (lpp_stable_scaled_bound operation result) < abs (lpp_stable_scaled_bound operation n)"
  using lpp_stable_scaled_quotient_modulo_progress[OF compatible evaluated denominator] by auto

definition lpp_stable_magnitude_progress_formula where
  "lpp_stable_magnitude_progress_formula rename a result =
    (let n=LPPEVariable (rename (LPPMagnitudeKey a));
         r=LPPEVariable (rename (LPPMagnitudeKey result)) in
      Conjunction [lpp_numeric_condition_formula (LPPIntLessEqual,LPPEConstant 0,r),
        lpp_numeric_condition_formula (LPPIntLess,r,n)])"

definition lpp_stable_magnitude_quotient_modulo_formula where
  "lpp_stable_magnitude_quotient_modulo_formula rename n d result =
    Conjunction [lpp_stable_magnitude_progress_formula rename n result,
      lpp_stable_magnitude_progress_formula rename (Fun (LPCUser ''2:prolog_data_2f2f'') [n,d]) result]"

ML \<open>
val checked = [@{thm lpp_magnitude_expression_value}, @{thm lpp_stable_magnitude_order},
  @{thm lpp_stable_magnitude_modulo_progress}, @{thm lpp_stable_magnitude_quotient_modulo_progress}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted magnitude condition dependency" else ();
\<close>
end
