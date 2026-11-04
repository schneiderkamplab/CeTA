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

lemma lpsh_tail_shape_transport:
  "lpp_evaluation_observation_check [] []
    [LPPOShape lpsh_keys (LPReturnShape 0) lpsh_pattern]
    (LPPOShape lpsh_keys (LPReturnShape 0) (Var ''tail''))"
  by (simp add: lpp_observations_shape_facts_def lpsh_keys_def lpsh_pattern_def eval_nat_numeral)

lemma lpsh_payload_shape_transport_rejected:
  "\<not>lpp_evaluation_observation_check [] []
    [LPPOShape lpsh_keys (LPReturnShape 0) lpsh_pattern]
    (LPPOShape lpsh_keys (LPReturnShape 0) (Var ''payload''))"
  by (simp add: lpp_observations_shape_facts_def lpsh_keys_def lpsh_pattern_def eval_nat_numeral)

lemma lpsh_empty_shape_transport_rejected:
  "\<not>lpp_evaluation_observation_check [] [] []
    (LPPOShape lpsh_keys (LPReturnShape 0) (Var ''tail''))"
  by (simp add: lpp_observations_shape_facts_def eval_nat_numeral)

lemma lpsh_wrong_grammar_transport_rejected:
  "\<not>lpp_evaluation_observation_check [] []
    [LPPOShape lpsh_keys (LPReturnShape 0) lpsh_pattern]
    (LPPOShape [[]] (LPReturnShape 0) (Var ''tail''))"
  by (simp add: lpp_observations_shape_facts_def lpsh_keys_def eval_nat_numeral)


text \<open>Ground observations justify ground constructor fields, but do not
turn an unconstrained ground value into a finite constructor spine.\<close>

definition lpsh_cell :: "string lp_cut_symbol lp_return_grammar" where
  "lpsh_cell = [[(LPCUser ''nil'',[]),
    (LPCUser ''cell'',[LPReturnGround,LPReturnAny])]]"

lemma lpsh_ground_field_transport:
  "lpp_evaluation_observation_check [] [] [LPPOGround (Var ''head'')]
    (LPPOShape lpsh_cell (LPReturnShape 0)
      (Fun (LPCUser ''cell'') [Var ''head'',Var ''tail'']))"
  by (simp add: lpp_observations_shape_facts_def lpsh_cell_def eval_nat_numeral)

lemma lpsh_missing_ground_field_rejected:
  "\<not>lpp_evaluation_observation_check [] [] []
    (LPPOShape lpsh_cell (LPReturnShape 0)
      (Fun (LPCUser ''cell'') [Var ''head'',Var ''tail'']))"
  by (simp add: lpp_observations_shape_facts_def lpsh_cell_def eval_nat_numeral)

lemma lpsh_ground_does_not_prove_spine:
  "\<not>lpp_evaluation_observation_check [] [] [LPPOGround (Var ''tail'')]
    (LPPOShape lpsh_cell (LPReturnShape 0) (Var ''tail''))"
  by (simp add: lpp_observations_shape_facts_def lpsh_cell_def eval_nat_numeral)

lemma lpsh_ground_does_not_prove_integer:
  "\<not>lpp_evaluation_observation_check [] [] [LPPOGround (Var ''head'')]
    (LPPOInteger (Var ''head''))"
  by (simp add: lpp_context_integer_from_def lpp_integer_term_def)

end
