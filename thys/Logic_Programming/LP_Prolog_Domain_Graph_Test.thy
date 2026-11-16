theory LP_Prolog_Domain_Graph_Test
 imports LP_Prolog_Domain_Graph_XML LP_Prolog_Scalar_Domain_Test
begin

definition graph_test_q where "graph_test_q = ''2:prolog_data_6669727374''"
definition graph_test_r where "graph_test_r = ''2:prolog_data_7365636f6e64''"
definition graph_test_actions where
 "graph_test_actions = [LPPDomainSet ''a'' scalar_test_step,LPPDomainSet ''b'' domain_test_step]"
definition graph_test_program where
 "graph_test_program = [
 (Fun (LPCUser graph_test_q) [Var ''x'',Var ''c''],[lpp_scalar_guard_goal (scalar_test_guard ''2:=<'')]),
 (Fun (LPCUser graph_test_q) [Var ''x'',Var ''c''],
  [lpp_scalar_guard_goal (scalar_test_guard ''2:>''),LPCAtom (Fun (LPCUser graph_test_r) [Var ''x'',Var ''c''])]),
 (Fun (LPCUser graph_test_r) [Var ''x'',Var ''c''],map lpp_domain_prefix_goal graph_test_actions @
  [LPCAtom (Fun (LPCUser graph_test_q) domain_test_outputs)])]"
definition graph_test_first where
 "graph_test_first dest = LPPDomainModule graph_test_q domain_test_observations 1 [''x'',''c'']
 [LPPDomainGuard (scalar_test_guard ''2:>'')] [Var ''x'',Var ''c'']
 [Some (LPPScalarParameter ''x''),Some (LPPScalarParameter ''c'')] domain_test_failures dest"
definition graph_test_second where
 "graph_test_second obs recipes dest = LPPDomainModule graph_test_r obs 0 [''x'',''c'']
 graph_test_actions domain_test_outputs recipes [] dest"
definition graph_test_modules where
 "graph_test_modules = [graph_test_first 1,graph_test_second domain_test_observations domain_test_recipes 0]"

lemma graph_coverage_and_transport_controls:
 "lpp_domain_graph_check graph_test_program graph_test_modules \<and>
 \<not>lpp_domain_graph_check graph_test_program [graph_test_first 1] \<and>
 \<not>lpp_domain_graph_check graph_test_program [graph_test_first 0,graph_test_second domain_test_observations domain_test_recipes 0] \<and>
 \<not>lpp_domain_graph_check graph_test_program [graph_test_first 1,graph_test_second domain_test_observations domain_test_recipes 7] \<and>
 \<not>lpp_domain_graph_check graph_test_program [graph_test_first 1,graph_test_second domain_test_observations [None,None] 0] \<and>
 \<not>lpp_domain_graph_check graph_test_program [graph_test_first 1,graph_test_second [Some LPPRecurrentInteger,Some LPPRecurrentInteger] domain_test_recipes 0] \<and>
 \<not>lpp_domain_graph_check graph_test_program (graph_test_modules@[graph_test_first 99])"
 by eval
end
