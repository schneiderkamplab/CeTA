theory LP_Prolog_Guarded_Domain_Graph_Test
 imports LP_Prolog_Guarded_Domain_Graph_XML
begin

definition guarded_test_gate where
 "guarded_test_gate f = LPPScalarCompare f (LPPScalarParameter ''x'') (LPPScalarLiteral (LPPMachineInteger 0))"
definition guarded_test_expression where
 "guarded_test_expression f = LPPScalarBinary f (LPPScalarParameter ''x'') (LPPScalarLiteral (LPPMachineInteger 1))"
definition guarded_test_module where
 "guarded_test_module sel f dest = LPPDomainModule ''1:counter'' [Some LPPRecurrentInteger] sel [''x'']
   [LPPDomainSet ''y'' (guarded_test_expression f)] [Var ''y''] [Some (LPPScalarParameter ''y'')] [] dest"
definition guarded_test_program where
 "guarded_test_program = map (\<lambda>(gate,f). (Fun (LPCUser ''1:counter'') [Var ''x''],
   [lpp_scalar_guard_goal (guarded_test_gate gate),
    lpp_domain_prefix_goal (LPPDomainSet ''y'' (guarded_test_expression f)),
    LPCAtom (Fun (LPCUser ''1:counter'') [Var ''y''])]))
   [(''2:<'',''2:prolog_data_2b''),(''2:>='',''2:prolog_data_2d'')]"
definition guarded_test_graph where
 "guarded_test_graph other dest = [LPPGuardedChoice (guarded_test_gate ''2:<'') (guarded_test_gate other)
   (guarded_test_module 0 ''2:prolog_data_2b'' 0) (guarded_test_module 1 ''2:prolog_data_2d'' dest)]"
lemma guarded_both_branches_checked:
 "lpp_guarded_domain_graph_check guarded_test_program (guarded_test_graph ''2:>='' 0)"
 by eval
lemma guarded_coverage_controls:
 "\<not>lpp_guarded_domain_graph_check guarded_test_program (guarded_test_graph ''2:>'' 0) \<and>
  \<not>lpp_guarded_domain_graph_check guarded_test_program (guarded_test_graph ''2:>='' 1) \<and>
  \<not>lpp_guarded_domain_graph_check (take 1 guarded_test_program) (guarded_test_graph ''2:>='' 0) \<and>
  \<not>lpp_guarded_domain_graph_check guarded_test_program
    [LPPGuardedPlain (guarded_test_module 0 ''2:prolog_data_2b'' 0)]"
 by code_simp
lemma unobserved_guard_is_not_total:
 "\<not>lpp_domain_guard_total (\<lambda>_.None) (guarded_test_gate ''2:<'')"
 by eval
end
