theory LP_Prolog_Integer_Expression_Shapes_Test
 imports LP_Prolog_Stopped_Mixed_XML
begin

definition expression_grammar where
 "expression_grammar = [[(LPCUser (lpp_integer_name 0),[]),
   (LPCUser (lpp_integer_name 1),[]),
   (LPCUser ''2:prolog_data_2b'',[LPReturnShape 0,LPReturnShape 0])]]"
lemma finite_integer_expressions:
 "lpp_integer_expression_shape expression_grammar (LPReturnShape 0)" by eval
lemma ground_child_insufficient:
 "\<not> lpp_integer_expression_shape [[(LPCUser ''2:prolog_data_2b'',
   [LPReturnGround,LPReturnShape 0])]] (LPReturnShape 0)" by eval
lemma arbitrary_child_insufficient:
 "\<not> lpp_integer_expression_shape [[(LPCUser ''2:prolog_data_2b'',
   [LPReturnAny,LPReturnShape 0])]] (LPReturnShape 0)" by eval
lemma floating_leaf_insufficient:
 "\<not> lpp_integer_expression_shape [[(LPCUser ''0:prolog_data_0070726f6c6f672e666c6f61743a30303030303030303030303030303030'',[])]] (LPReturnShape 0)" by eval
lemma ground_shape_insufficient:
 "\<not> lpp_integer_expression_shape expression_grammar LPReturnGround" by eval
lemma arithmetic_arity_checked:
 "\<not> lpp_integer_expression_shape [[(LPCUser ''2:prolog_data_2b'',[LPReturnShape 0])]] (LPReturnShape 0)" by eval
lemma expression_shape_leaf_observation:
 "lpp_observed_evaluated_integers (LPPOShape expression_grammar (LPReturnShape 0) (Var ''counter'')) = [Var ''counter'']" by eval
lemma expression_shape_must_be_observed:
 "\<not> lpp_check_evaluated_expression [] [(''leaf'',Var ''counter'')] (LPPEVariable ''leaf'')" by eval
lemma legacy_observation_selection:
 "lpp_stable_selected_observations [LPPOShape expression_grammar (LPReturnShape 0) (Var ''counter'')] [] = []" by eval
lemma shape_observation_selection:
 "lpp_stable_selected_observations [LPPOShape expression_grammar (LPReturnShape 0) (Var ''counter'')] [LPPStableIgnoredCondition] =
 [LPPOShape expression_grammar (LPReturnShape 0) (Var ''counter'')]" by eval
end
