theory LP_Prolog_Scalar_Recurrence_Test
 imports LP_Prolog_Scalar_Recurrence_XML
begin

definition scalar_test_q where "scalar_test_q = ''2:prolog_data_726570656174''"
definition scalar_test_guard where
 "scalar_test_guard f = LPPScalarCompare f (LPPScalarParameter ''x'') (LPPScalarLiteral (LPPMachineInteger 0))"
definition scalar_test_step where
 "scalar_test_step = LPPScalarBinary ''2:prolog_data_2d'' (LPPScalarParameter ''x'') (LPPScalarLiteral (LPPMachineInteger 1))"
definition scalar_test_actions where
 "scalar_test_actions = [LPPScalarPrefixGuard (scalar_test_guard ''2:>''), LPPScalarPrefixCut]"
definition scalar_test_outputs where
 "scalar_test_outputs = [lpp_scalar_template_term scalar_test_step,Var ''z'']"
definition scalar_test_program where
 "scalar_test_program = [
 (Fun (LPCUser scalar_test_q) [Var ''x'',Var ''y''],[lpp_scalar_guard_goal (scalar_test_guard ''2:=<'')]),
 (Fun (LPCUser scalar_test_q) [Var ''x'',Var ''y''],
  map lpp_scalar_prefix_goal scalar_test_actions @
  [LPCAtom (Fun (LPCUser scalar_test_q) scalar_test_outputs),
   LPCAtom (Fun (LPCUser ''2:is'') [Var ''y'',lpp_integer_term 0])])]"
definition scalar_test_failures :: "(string list * lpp_scalar_guard list * lpp_scalar_guard) list" where
 "scalar_test_failures = [([''x'',''y''],[],scalar_test_guard ''2:=<'')]"
definition scalar_test_observations where
 "scalar_test_observations = [Some (LPPMachineFloat 4850376798678024192),None]"

lemma growing_syntax_fixed_scalar_checked:
 "lpp_check_scalar_recurrence scalar_test_program scalar_test_q [True,False]
 scalar_test_observations 1 [''x'',''y''] scalar_test_actions scalar_test_outputs
 [Some scalar_test_step,None] scalar_test_failures"
 by eval
lemma small_scalar_not_fixed:
 "\<not>lpp_check_scalar_recurrence scalar_test_program scalar_test_q [True,False]
 [Some (LPPMachineInteger 8),None] 1 [''x'',''y''] scalar_test_actions scalar_test_outputs
 [Some scalar_test_step,None] scalar_test_failures"
 by eval
lemma missing_earlier_failure_rejected:
 "\<not>lpp_check_scalar_recurrence scalar_test_program scalar_test_q [True,False]
 scalar_test_observations 1 [''x'',''y''] scalar_test_actions scalar_test_outputs
 [Some scalar_test_step,None] []"
 by eval
lemma missing_output_dependency_rejected:
 "\<not>lpp_check_scalar_recurrence scalar_test_program scalar_test_q [True,False]
 scalar_test_observations 1 [''x'',''y''] scalar_test_actions scalar_test_outputs
 [None,None] scalar_test_failures"
 by eval
lemma missing_cut_rejected:
 "\<not>lpp_check_scalar_recurrence scalar_test_program scalar_test_q [True,False]
 scalar_test_observations 1 [''x'',''y''] (take 1 scalar_test_actions) scalar_test_outputs
 [Some scalar_test_step,None] scalar_test_failures"
 by eval
lemma nonfinite_initial_observation_rejected:
 "\<not>lpp_check_scalar_recurrence scalar_test_program scalar_test_q [True,False]
 [Some (LPPMachineFloat 9218868437227405312),None] 1 [''x'',''y''] scalar_test_actions scalar_test_outputs
 [Some scalar_test_step,None] scalar_test_failures"
 by eval
lemma wrong_parameter_rejected:
 "\<not>lpp_check_scalar_recurrence scalar_test_program scalar_test_q [True,False]
 scalar_test_observations 1 [''x'',''y''] scalar_test_actions scalar_test_outputs
 [Some (LPPScalarParameter ''z''),None] scalar_test_failures"
 by eval

end
