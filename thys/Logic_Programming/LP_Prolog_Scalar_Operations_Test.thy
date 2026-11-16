theory LP_Prolog_Scalar_Operations_Test
 imports LP_Prolog_Scalar_Domain_Expressions
begin
lemma signed_integer_operations:
 "lpp_scalar_binary ''2:prolog_data_2f2f'' (LPPMachineInteger (-7)) (LPPMachineInteger 3) = Some (LPPMachineInteger (-2))"
 "lpp_scalar_binary ''2:prolog_data_2f2f'' (LPPMachineInteger 7) (LPPMachineInteger (-3)) = Some (LPPMachineInteger (-2))"
 "lpp_scalar_binary ''2:prolog_data_6d6f64'' (LPPMachineInteger (-7)) (LPPMachineInteger 3) = Some (LPPMachineInteger 2)"
 "lpp_scalar_binary ''2:prolog_data_6d6f64'' (LPPMachineInteger 7) (LPPMachineInteger (-3)) = Some (LPPMachineInteger (-2))"
 by eval+
lemma integer_operation_errors:
 "list_all (\<lambda>f. lpp_scalar_binary f (LPPMachineInteger 1) (LPPMachineInteger 0) = None \<and>
 lpp_scalar_binary f (LPPMachineFloat 0) (LPPMachineInteger 2) = None \<and>
 lpp_scalar_binary f (LPPMachineInteger 1) (LPPMachineFloat 0) = None)
 [''2:prolog_data_2f2f'',''2:prolog_data_6d6f64'']"
 by eval
lemma integer_domain_divisor_obligation:
 "list_all (\<lambda>f.
 lpp_recurrent_scalar_binary f LPPRecurrentInteger (LPPRecurrentFixed (LPPMachineInteger 2)) = Some LPPRecurrentInteger \<and>
 lpp_recurrent_scalar_binary f LPPRecurrentInteger (LPPRecurrentFixed (LPPMachineInteger 0)) = None \<and>
 lpp_recurrent_scalar_binary f LPPRecurrentInteger LPPRecurrentInteger = None \<and>
 lpp_recurrent_scalar_binary f LPPRecurrentInteger (LPPRecurrentFixed (LPPMachineFloat 0)) = None)
 [''2:prolog_data_2f2f'',''2:prolog_data_6d6f64'']"
 by eval
end
