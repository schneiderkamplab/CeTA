theory LP_Prolog_Shape_Observations_Test
  imports LP_Prolog_Finite_Shape_Receipt LP_Prolog_Finite_Triple_XML
begin

definition lpsh_keys :: "string lp_cut_symbol lp_return_grammar" where
  "lpsh_keys = [[(LPCUser ''nil'',[]),
    (LPCUser ''cons'',[LPReturnShape 0,LPReturnShape 0]),
    (LPCUser ''pair'',[LPReturnGround,LPReturnAny])]]"

definition lpsh_pattern :: "(string lp_cut_symbol,string) term" where
  "lpsh_pattern = Fun (LPCUser ''cons'')
    [Fun (LPCUser ''pair'') [Var ''key'',Var ''payload''],Var ''tail'']"

lemma lpsh_observed_key_ground:
  "lpp_shape_seed_check lpsh_keys []
    ([],[],[LPPOShape lpsh_keys (LPReturnShape 0) lpsh_pattern])
    [(LPReturnGround,''key''),(LPReturnShape 0,''tail'')]"
  by (simp add: lpsh_keys_def lpsh_pattern_def lp_return_shape_ground_vars_def lpp_observations_ground_def eval_nat_numeral)

lemma lpsh_unobserved_payload_rejected:
  "\<not>lpp_shape_seed_check lpsh_keys []
    ([],[],[LPPOShape lpsh_keys (LPReturnShape 0) lpsh_pattern]) [(LPReturnGround,''payload'')]"
  by (simp add: lpsh_keys_def lpsh_pattern_def lp_return_shape_ground_vars_def lpp_observations_ground_def eval_nat_numeral)

lemma lpsh_resumed_empty_context_rejected:
  "\<not>lpp_shape_seed_check lpsh_keys [] ([],[],[]) [(LPReturnGround,''key'')]"
  by (simp add: lpp_observations_ground_def)

lemma lpsh_wrong_grammar_rejected:
  "\<not>lpp_shape_seed_check [[]] []
    ([],[],[LPPOShape lpsh_keys (LPReturnShape 0) lpsh_pattern]) [(LPReturnShape 0,''tail'')]"
  by (simp add: lpsh_keys_def)

lemma lpsh_not_integer_evidence:
  "\<not>lpp_check_numeric_observation K (LPPOShape lpsh_keys (LPReturnShape 0) t) numeric_test"
  by simp

end
