theory LP_Prolog_Numeric_Return_Test
 imports LP_Prolog_Value_Order_Rows LP_Prolog_Stable_Order_Backend_XML
begin

definition numeric_return_test_guards :: "string lpp_success_guard list" where
 "numeric_return_test_guards = [LPPSEvaluates (Var ''n'') (Var ''out''),
   LPPSNumeric 1 (Var ''n'') (Var ''limit''),
   LPPSNumeric 2 (Fun (LPCUser ''2:prolog_data_6d6f64'') [Var ''n'',lpp_integer_term 1]) (lpp_integer_term 0)]"

definition numeric_return_test_program :: "string lpp_success_clause list" where
 "numeric_return_test_program = [((''renamed_helper'',[Var ''n'',Var ''limit'',Var ''out'']),[],numeric_return_test_guards)]"

definition numeric_return_test_order :: lpp_order_summaries where
 "numeric_return_test_order signature = (if signature=(''renamed_helper'',3) then [(False,LPPOrderArgument 1,2)] else [])"

definition numeric_return_test_values where
 "numeric_return_test_values signature = (if signature=(''renamed_helper'',3) then [0] else [])"

definition numeric_return_test_receipts where
 "numeric_return_test_receipts = [[([LPPOrderComparedEvaluation 0 1 (LPPOrderKnown 0) ''out''],0)]]"

lemma compared_return_order_checked:
 "lpp_check_order_program numeric_return_test_order numeric_return_test_program numeric_return_test_receipts"
 by eval

lemma successful_modulo_value_domain_checked:
 "lpp_check_value_program numeric_return_test_values numeric_return_test_program"
 by eval

lemma comparison_alone_does_not_type_values:
 "\<not>lpp_check_value_program numeric_return_test_values
   [((''renamed_helper'',[Var ''n'',Var ''limit'',Var ''out'']),[],take 2 numeric_return_test_guards)]"
 by eval

lemma comparison_order_needs_integer_evidence:
 "\<not>lpp_check_order_program numeric_return_test_order
   [((''renamed_helper'',[Var ''n'',Var ''limit'',Var ''out'']),[],take 2 numeric_return_test_guards)] numeric_return_test_receipts"
 by eval

lemma missing_return_comparison_rejected:
 "\<not>lpp_check_order_program numeric_return_test_order numeric_return_test_program
   [[([LPPOrderComparedEvaluation 0 5 (LPPOrderKnown 0) ''out''],0)]]"
 by eval

lemma unknown_conditional_input_rejected:
 "lpp_value_order_use (\<lambda>_. []) numeric_return_test_order
   [(''renamed_helper'',[Var ''x'',Var ''bound'',Var ''result''])] (0,0) = None"
 by eval

lemma value_order_selection_requires_actual_dependency:
 "\<not>lpp_check_value_order_selection numeric_return_test_values numeric_return_test_order
   (((''entry'',[]),[],(''exit'',[]),[]),[]) (Some 0,[Var ''invented''],[])"
 by eval

lemma numeric_success_guard_xml:
 "case_sum_bot False (\<lambda>_. False) (\<lambda>g. g=LPPSNumeric 1 (Var ''x'') (Var ''y''))
   (parse_xml_string lpp_success_guard_parser
    ''<numericSuccessGuard><comparison>1</comparison><var>x</var><var>y</var></numericSuccessGuard>'')"
 by eval

end
