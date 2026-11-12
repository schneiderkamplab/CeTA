theory LP_Prolog_Equation_Link_Ground_Test
 imports LP_Prolog_Evaluation_Link
begin

lemma ground_after_resolution_equation:
  "''result'' \<in> lpp_equation_link_ground
    ([],[],[LPPOEquation (Var ''result'') (Fun (LPCUser ''pair'') [Var ''left'',Var ''right''])])
    [''left''] [(Var ''right'',Fun (LPCUser ''constant'') [])]"
  by (simp add: lpp_observations_equation_ground_def lpp_observations_ground_def numeral_eq_Suc)

lemma missing_resolution_equation_rejects:
  "''result'' \<notin> lpp_equation_link_ground
    ([],[],[LPPOEquation (Var ''result'') (Fun (LPCUser ''pair'') [Var ''left'',Var ''right''])])
    [''left''] []"
  by (simp add: lpp_observations_equation_ground_def lpp_observations_ground_def numeral_eq_Suc)

lemma cyclic_equation_cannot_seed_finiteness:
  "''cycle'' \<notin> lpp_equation_link_ground ([],[],[]) []
    [(Var ''cycle'',Fun (LPCUser ''cell'') [Var ''cycle''])]"
  by (simp add: lpp_observations_equation_ground_def lpp_observations_ground_def numeral_eq_Suc)

lemma unrelated_ground_input_cannot_seed_cycle:
  "''cycle'' \<notin> lpp_equation_link_ground ([],[],[]) [''other'']
    [(Var ''cycle'',Fun (LPCUser ''cell'') [Var ''cycle''])]"
  by (simp add: lpp_observations_equation_ground_def lpp_observations_ground_def numeral_eq_Suc)

end
