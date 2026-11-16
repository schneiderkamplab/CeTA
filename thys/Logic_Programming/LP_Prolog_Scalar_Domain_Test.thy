theory LP_Prolog_Scalar_Domain_Test
 imports LP_Prolog_Scalar_Domain_XML LP_Prolog_Scalar_Recurrence_Test
begin

definition domain_test_step where
 "domain_test_step = LPPScalarBinary ''2:prolog_data_2b'' (LPPScalarParameter ''c'') (LPPScalarLiteral (LPPMachineInteger 1))"
definition domain_test_actions where
 "domain_test_actions = [LPPDomainGuard (scalar_test_guard ''2:>''),
   LPPDomainSet ''a'' scalar_test_step, LPPDomainSet ''b'' domain_test_step]"
definition domain_test_outputs :: "(string lp_cut_symbol,string) term list" where
 "domain_test_outputs = [Var ''a'',Var ''b'']"
definition domain_test_program where
 "domain_test_program = [
 (Fun (LPCUser scalar_test_q) [Var ''x'',Var ''c''],[lpp_scalar_guard_goal (scalar_test_guard ''2:=<'')]),
 (Fun (LPCUser scalar_test_q) [Var ''x'',Var ''c''],
  map lpp_domain_prefix_goal domain_test_actions @
  [LPCAtom (Fun (LPCUser scalar_test_q) domain_test_outputs)])]"
definition domain_test_observations where
 "domain_test_observations = [Some (LPPRecurrentFixed (LPPMachineFloat 4850376798678024192)), Some LPPRecurrentInteger]"
definition domain_test_recipes where
 "domain_test_recipes = [Some (LPPScalarParameter ''a''),Some (LPPScalarParameter ''b'')]"
definition domain_test_failures :: "(string list * lpp_scalar_guard list * lpp_scalar_guard) list" where
 "domain_test_failures = [([''x'',''c''],[],scalar_test_guard ''2:=<'')]"
definition domain_test_check where
 "domain_test_check observations actions recipes failures =
 lpp_domain_recurrence_check domain_test_program scalar_test_q observations 1 [''x'',''c''] actions domain_test_outputs recipes failures"

lemma recurrence_domain_controls:
 "domain_test_check domain_test_observations domain_test_actions domain_test_recipes domain_test_failures \<and>
 \<not>domain_test_check domain_test_observations (take 2 domain_test_actions) domain_test_recipes domain_test_failures \<and>
 \<not>domain_test_check domain_test_observations domain_test_actions domain_test_recipes [] \<and>
 \<not>domain_test_check domain_test_observations domain_test_actions [None,None] domain_test_failures \<and>
 \<not>domain_test_check [Some (LPPRecurrentFixed (LPPMachineInteger 8)),Some LPPRecurrentInteger] domain_test_actions domain_test_recipes domain_test_failures \<and>
 \<not>domain_test_check [Some LPPRecurrentInteger,Some LPPRecurrentInteger] domain_test_actions domain_test_recipes domain_test_failures \<and>
 \<not>domain_test_check [Some (LPPRecurrentFixed (LPPMachineFloat 4850376798678024192)),None] domain_test_actions domain_test_recipes domain_test_failures"
 by eval

lemma integer_domain_initialization_controls:
 "lpp_domain_outputs_check (\<lambda>_.None) [Some LPPRecurrentInteger] [lpp_integer_term 0]
 [Some (LPPScalarLiteral (LPPMachineInteger 0))] \<and>
 \<not>lpp_domain_outputs_check (\<lambda>_.None) [Some LPPRecurrentInteger] [lpp_scalar_template_term (LPPScalarLiteral (LPPMachineFloat 4850376798678024192))]
 [Some (LPPScalarLiteral (LPPMachineFloat 4850376798678024192))]"
 by eval
end
