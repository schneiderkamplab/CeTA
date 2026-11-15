theory LP_Prolog_Evaluated_Integer_Test
  imports LP_Prolog_Stable_Numeric_Conditions
begin

lemma magnitude_evaluation_accepts_actual_result:
  "lpp_check_stable_numeric_observation K (LPPOEvaluation a b)
    (LPPStableMagnitudeEvaluationCondition a b)"
  by simp

lemma magnitude_evaluation_rejects_groundness:
  "\<not> lpp_check_stable_numeric_observation K (LPPOGround a)
    (LPPStableMagnitudeEvaluationCondition a b)"
  by simp

lemma magnitude_evaluation_rejects_wrong_result:
  "b\<noteq>c \<Longrightarrow> \<not> lpp_check_stable_numeric_observation K (LPPOEvaluation a b)
    (LPPStableMagnitudeEvaluationCondition a c)"
  by simp


lemma evaluated_integer_requires_observation:
  "\<not> lpp_check_evaluated_expression [] [(x,t)] (LPPEVariable x)"
  by (simp add: lpp_check_evaluated_expression_def)

lemma evaluated_integer_requires_distinct_bindings:
  "\<not> lpp_check_evaluated_expression ambient [(x,t),(x,u)] e"
  by (simp add: lpp_check_evaluated_expression_def)

lemma evaluated_integer_cannot_use_unbound_leaf:
  "\<not> lpp_check_evaluated_expression ambient [] (LPPEVariable x)"
  by (simp add: lpp_check_evaluated_expression_def)

lemma evaluated_integer_requires_path_checker:
  "\<not> lpp_check_stable_numeric_observation K observation
    (LPPStableEvaluatedIntegerCondition bindings e)"
  by simp

lemma floor_order_rejects_equality:
  "\<not> lpp_check_stable_path_observation K ambient
    (LPPOComparison LPPIntEqual a b) (LPPStableFloorOrderCondition a b)"
  by simp

lemma evaluated_integer_uses_checked_literal_type:
  "lpp_check_stable_path_observation [x] [] observation
    (LPPStableEvaluatedIntegerCondition [(v,Var x)]
      (LPPEAdd (LPPEVariable v) (LPPEConstant 1)))"
  by (simp add: lpp_check_evaluated_expression_def)

lemma evaluated_integer_rejects_missing_literal_type:
  "\<not> lpp_check_stable_path_observation [] [] observation
    (LPPStableEvaluatedIntegerCondition [(v,Var x)]
      (LPPEAdd (LPPEVariable v) (LPPEConstant 1)))"
  by (simp add: lpp_check_evaluated_expression_def)

ML \<open>
val checked = [@{thm evaluated_integer_uses_checked_literal_type},
 @{thm evaluated_integer_rejects_missing_literal_type},@{thm evaluated_integer_requires_observation},
 @{thm evaluated_integer_requires_distinct_bindings},
 @{thm evaluated_integer_cannot_use_unbound_leaf},
 @{thm evaluated_integer_requires_path_checker}, @{thm floor_order_rejects_equality}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted evaluated integer test dependency" else ();
\<close>
end
