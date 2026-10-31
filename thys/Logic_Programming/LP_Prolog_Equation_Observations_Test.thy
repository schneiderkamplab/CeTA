theory LP_Prolog_Equation_Observations_Test
 imports LP_Prolog_Evaluation_Context
begin

lemma shared_field_groundness:
  "lpp_evaluation_observation_check [] []
    [LPPOEquation (Var ''whole'') (Fun (LPCUser ''cell'') [Var ''field'']), LPPOGround (Var ''whole'')]
    (LPPOGround (Var ''field''))"
  by (simp add: lpp_observations_equation_ground_def lpp_observations_ground_def numeral_eq_Suc)

lemma missing_equation_rejects:
  "\<not>lpp_evaluation_observation_check [] [] [LPPOGround (Var ''whole'')]
    (LPPOGround (Var ''field''))"
  by (simp add: lpp_observations_equation_ground_def lpp_observations_ground_def numeral_eq_Suc)

lemma cyclic_equation_is_not_finite:
  "\<not>lpp_evaluation_observation_check [] []
    [LPPOEquation (Var ''x'') (Fun (LPCUser ''f'') [Var ''x''])] (LPPOGround (Var ''x''))"
  by (simp add: lpp_observations_equation_ground_def lpp_observations_ground_def numeral_eq_Suc)

lemma equation_requires_initialization:
  "\<not>lpp_evaluation_observation_check [] [] [] (LPPOEquation (Var ''whole'') (Var ''field''))"
  by simp

lemma reflexive_equation_initializes:
  "lpp_evaluation_observation_check [] [] [] (LPPOEquation t t)"
  by simp

end
