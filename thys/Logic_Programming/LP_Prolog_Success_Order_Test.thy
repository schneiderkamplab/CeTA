theory LP_Prolog_Success_Order_Test
  imports LP_Prolog_Success_Order_Rows LP_Prolog_Stable_Order_Backend_XML
begin

lemma order_positioned_row_parser:
  "case_sum_bot False (\<lambda>_. False) (\<lambda>r. r=(Some 1,[]))
    (parse_xml_string lpp_order_row_parser
    ''<positionedRow><observationPosition>1</observationPosition><uses/></positionedRow>'')"
  by eval

lemma order_legacy_row_parser:
  "case_sum_bot False (\<lambda>_. False) (\<lambda>r. r=(None,[]))
    (parse_xml_string lpp_order_row_parser ''<row/>'')"
  by eval

lemma order_observations_keep_original_suffix:
  "lpp_order_insert (Some 1) [a,b] [c,d] = [a,c,d,b]"
  by (simp add: lpp_order_insert_def)

lemma order_legacy_observations_append:
  "lpp_order_insert None [a,b] [c,d] = [a,b,c,d]"
  by (simp add: lpp_order_insert_def)


definition order_test_table :: lpp_order_summaries where
  "order_test_table signature = (if signature=(''walk'',2) then [(True,LPPOrderArgument 0,1)]
    else if signature=(''wrapper'',1) then [(True,LPPOrderConstant 2,0)] else [])"

definition order_test_program :: "string lpp_success_clause list" where
  "order_test_program = [
    ((''walk'',[Var ''x'',Var ''y'']),[],[LPPSEvaluates (Var ''x'') (Var ''y'')]),
    ((''walk'',[Var ''x'',Var ''y'']),[(''walk'',[Fun (LPCUser ''2:prolog_data_2b'') [Var ''x'',lpp_integer_term 1],Var ''y''])],[]),
    ((''wrapper'',[Var ''y'']),[(''walk'',[lpp_integer_term 2,Var ''y''])],[])]"

definition order_test_receipts where
  "order_test_receipts = [
    [([LPPOrderEvaluation 0 (LPPOrderKnown 0) ''y''],0)],
    [([LPPOrderHelper 0 0 (LPPOrderShift (LPPOrderKnown 0) 1) ''y''],0)],
    [([LPPOrderHelper 0 0 (LPPOrderKnown 0) ''y''],0)]]"

lemma order_contract_recursive_wrapper:
  "lpp_check_order_program order_test_table order_test_program order_test_receipts"
  by (simp add: lpp_check_order_program_def lpp_check_order_rows_def lpp_check_order_clause_def
    order_test_table_def order_test_program_def order_test_receipts_def lpp_order_relation_def
    lpp_numeric_enriched_guards_def lpp_numeric_call_guards_def lpp_numeric_model_check_def lpp_numeric_return_guards_def)

lemma order_contract_missing_clause_receipt:
  "\<not>lpp_check_order_program order_test_table order_test_program (tl order_test_receipts)"
  by (simp add: lpp_check_order_program_def lpp_check_order_rows_def lpp_check_order_clause_def
    order_test_table_def order_test_program_def order_test_receipts_def lpp_order_relation_def
    lpp_numeric_enriched_guards_def lpp_numeric_call_guards_def lpp_numeric_model_check_def lpp_numeric_return_guards_def)

lemma order_contract_missing_helper_dependency:
  "\<not>lpp_check_order_program (\<lambda>signature. if signature=(''wrapper'',1) then [(True,LPPOrderConstant 2,0)] else [])
    order_test_program order_test_receipts"
  by (simp add: lpp_check_order_program_def lpp_check_order_rows_def lpp_check_order_clause_def
    order_test_program_def order_test_receipts_def
    lpp_numeric_enriched_guards_def lpp_numeric_call_guards_def lpp_numeric_model_check_def lpp_numeric_return_guards_def)

lemma order_contract_wrong_shift_direction:
  "\<not>lpp_check_order_bound True [Var ''x'']
    (Fun (LPCUser ''2:prolog_data_2b'') [Var ''x'',lpp_integer_term (-1)])
    (LPPOrderShift (LPPOrderKnown 0) (-1))"
  by (simp add: lpp_order_relation_def)

lemma order_use_requires_actual_prefix:
  "lpp_order_use order_test_table [] (0,0) = None"
  by (simp add: lpp_order_use_def)

lemma order_use_does_not_erase_conditional_input:
  "lpp_order_use order_test_table [(''walk'',[Var ''x'',Var ''y''])] (0,0) = None"
  by (simp add: lpp_order_use_def order_test_table_def)

lemma order_use_constant_wrapper:
  "lpp_order_use order_test_table [(''wrapper'',[Var ''y''])] (0,0) = Some (True,2,Var ''y'')"
  by (simp add: lpp_order_use_def order_test_table_def)

end
