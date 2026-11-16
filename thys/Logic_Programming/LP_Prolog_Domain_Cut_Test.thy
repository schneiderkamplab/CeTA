theory LP_Prolog_Domain_Cut_Test
 imports LP_Prolog_Guarded_Domain_Graph_Test
begin

definition cut_test_update where
 "cut_test_update = LPPDomainSet ''y'' (LPPScalarBinary ''2:prolog_data_2b''
   (LPPScalarParameter ''x'') (LPPScalarLiteral (LPPMachineInteger 1)))"
definition cut_test_program where
 "cut_test_program = [(Fun (LPCUser ''1:counter'') [Var ''x''],
   [LPCCut 0,lpp_domain_prefix_goal cut_test_update,LPCCut 0,
    LPCAtom (Fun (LPCUser ''1:counter'') [Var ''y''])])]"
definition cut_test_module where
 "cut_test_module = LPPDomainModule ''1:counter'' [Some LPPRecurrentInteger] 0 [''x''] []
    [Var ''y''] [Some (LPPScalarParameter ''y'')] [] 0"
lemma cut_two_segments_checked:
 "lpp_guarded_domain_graph_check cut_test_program
   [LPPGuardedCut [[],[cut_test_update]] cut_test_module]"
 by eval
lemma cut_coverage_controls:
 "\<not>lpp_guarded_domain_graph_check cut_test_program [LPPGuardedCut [[cut_test_update]] cut_test_module]"
 "\<not>lpp_guarded_domain_graph_check cut_test_program [LPPGuardedCut [[],[]] cut_test_module]"
 "\<not>lpp_guarded_domain_graph_check cut_test_program [LPPGuardedPlain cut_test_module]"
 by code_simp+
lemma cut_preserves_outer_alternatives:
 "lp_cut_prune mark (LPCClause goals c mark # LPCBarrier mark # outer) = LPCBarrier mark # outer"
 by simp
end
