theory LP_Prolog_Natural_Return_Context
 imports LP_Prolog_Evaluation_Comparison LP_Prolog_Evaluation_Integer_Test
begin

text \<open>A nonnegative integer result supplies both typing and a lower bound.
The caller proves the result property and freshness separately. This rule does
not identify the requested output with that result or modify saved frames.\<close>
definition lpp_add_natural_observation where
  "lpp_add_natural_observation a ctx =
    lpp_add_numeric_observation (LPPOComparison LPPIntLessEqual (lpp_integer_term 0) a)
      (lpp_add_integer_observation a ctx)"

lemma lpp_natural_comparison:
  assumes "0\<le>n"
  shows "lpp_finite_compare_outcome LPPIntLessEqual (lpp_integer_value 0)
    (lpp_integer_value n) (LPPBuiltinSuccess LPIVar)"
  using assms
  by (simp only: lpp_finite_comparison_integer[OF lpp_integer_evaluation.literal lpp_integer_evaluation.literal]
    lpp_integer_compare_outcome_exact[OF lpp_integer_evaluation.literal lpp_integer_evaluation.literal]) simp

lemma lpp_add_evaluation_natural_holds:
  assumes held: "lpp_evaluation_context_holds E P ctx eta"
    and result: "lp_ieval a eta=lpp_integer_value n" and bound: "0\<le>n"
  shows "lpp_evaluation_context_holds E P (lpp_add_natural_observation a ctx) eta"
  unfolding lpp_add_natural_observation_def
  apply (rule lpp_add_evaluation_numeric_holds)
   apply (rule lpp_add_evaluation_integer_holds[OF held])
   apply (simp add: result lpp_is_integer_def)
  using lpp_natural_comparison[OF bound] by (simp add: result)

ML \<open>
val checked = [@{thm lpp_add_evaluation_natural_holds}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted natural return context" else ();
\<close>
end
