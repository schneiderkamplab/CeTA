theory LP_Prolog_Evaluation_XML
 imports LP_Prolog_Evaluation_Control LP_Prolog_Context_Module_XML
begin

definition lpp_evaluation_types_parser where
  "lpp_evaluation_types_parser tag = xml_many tag lpp_transfer_fact_parser id"

definition lpp_evaluation_action_parser where
  "lpp_evaluation_action_parser =
    (XMLdo (STR ''cut'') {
      action\<leftarrow>lpc_return_action_parser;
      yes\<leftarrow>lpp_evaluation_types_parser (STR ''yesTypes'');
      no\<leftarrow>lpp_evaluation_types_parser (STR ''noTypes'');
      xml_return (LPPEPrimitive (LPPEOrdinary action yes no))}) XMLor
    (XMLdo (STR ''integerTest'') {
      a\<leftarrow>lpc_term_parser; gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      yes\<leftarrow>lpc_link_parser; no\<leftarrow>lpc_link_parser;
      yf\<leftarrow>lpp_evaluation_types_parser (STR ''yesTypes'');
      nf\<leftarrow>lpp_evaluation_types_parser (STR ''noTypes'');
      xml_return (LPPEPrimitive (LPPEIntegerTest a gs active saved yes no yf nf))}) XMLor
    (XMLdo (STR ''termTest'') {
      f\<leftarrow>xml_text (STR ''predicate''); a\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      yes\<leftarrow>lpc_link_parser; no\<leftarrow>lpc_link_parser;
      yf\<leftarrow>lpp_evaluation_types_parser (STR ''yesTypes'');
      nf\<leftarrow>lpp_evaluation_types_parser (STR ''noTypes'');
      xml_return (LPPEPrimitive (LPPETermTest f a gs active saved yes no yf nf))}) XMLor
    (XMLdo (STR ''groundDisequality'') {
      a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      yes\<leftarrow>lpc_link_parser; no\<leftarrow>lpc_link_parser;
      yf\<leftarrow>lpp_evaluation_types_parser (STR ''yesTypes'');
      nf\<leftarrow>lpp_evaluation_types_parser (STR ''noTypes'');
      xml_return (LPPEPrimitive (LPPEGroundDisequality a b gs active saved yes no yf nf))}) XMLor
    (XMLdo (STR ''conditionalBranch'') {
      c\<leftarrow>lpc_term_parser; y\<leftarrow>lpc_term_parser; z\<leftarrow>lpc_term_parser;
      cs\<leftarrow>xml_many (STR ''conditionGoals'') lpc_goal_parser id;
      ys\<leftarrow>xml_many (STR ''thenGoals'') lpc_goal_parser id;
      zs\<leftarrow>xml_many (STR ''elseGoals'') lpc_goal_parser id;
      m\<leftarrow>xml_nat (STR ''commitScope''); n\<leftarrow>xml_nat (STR ''localScope'');
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      e\<leftarrow>lpc_link_parser; fs\<leftarrow>lpp_evaluation_types_parser (STR ''types'');
      xml_return (LPPEPrimitive (LPPEBranch c y z cs ys zs m n gs active saved e fs))}) XMLor
    (XMLdo (STR ''opaqueProbe'') {
      f\<leftarrow>xml_text (STR ''predicate''); g\<leftarrow>xml_text (STR ''targetPredicate'');
      argv\<leftarrow>xml_many (STR ''arguments'') lpc_term_parser id;
      m\<leftarrow>xml_nat (STR ''commitScope''); n\<leftarrow>xml_nat (STR ''localScope'');
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      e\<leftarrow>lpc_link_parser; fs\<leftarrow>lpp_evaluation_types_parser (STR ''types'');
      xml_return (LPPEPrimitive (LPPEProbe f g argv m n gs active saved e fs))}) XMLor
    (XMLdo (STR ''rationalDisequality'') {
      a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      yes\<leftarrow>lpc_link_parser; no\<leftarrow>lpc_link_parser;
      yf\<leftarrow>lpp_evaluation_types_parser (STR ''yesTypes'');
      nf\<leftarrow>lpp_evaluation_types_parser (STR ''noTypes'');
      xml_return (LPPEPrimitive (LPPERationalDisequality a b gs active saved yes no yf nf))}) XMLor
    (XMLdo (STR ''identityTest'') {
      f\<leftarrow>xml_text (STR ''predicate''); a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      yes\<leftarrow>lpc_link_parser; no\<leftarrow>lpc_link_parser;
      yf\<leftarrow>lpp_evaluation_types_parser (STR ''yesTypes'');
      nf\<leftarrow>lpp_evaluation_types_parser (STR ''noTypes'');
      xml_return (LPPEPrimitive (LPPEIdentity f a b gs active saved yes no yf nf))}) XMLor
    (XMLdo (STR ''equationRewrite'') {
      a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      e\<leftarrow>lpc_link_parser; fs\<leftarrow>lpp_evaluation_types_parser (STR ''types'');
      xml_return (LPPEEquationRewrite a b gs active saved e fs)}) XMLor
    (XMLdo (STR ''clauseEquationRewrite'') {
      a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      c\<leftarrow>xml_nat (STR ''index''); m\<leftarrow>xml_nat (STR ''scope'');
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      e\<leftarrow>lpc_link_parser; fs\<leftarrow>lpp_evaluation_types_parser (STR ''types'');
      xml_return (LPPEClauseEquationRewrite a b gs c m active saved e fs)}) XMLor
    (XMLdo (STR ''finiteEvaluationError'') {
      a\<leftarrow>lpc_term_parser; e\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      xml_return (LPPEEvaluationError a e gs active saved)}) XMLor
    (XMLdo (STR ''finiteComparisonError'') {
      f\<leftarrow>xml_text (STR ''predicate''); comparison\<leftarrow>lpp_numeric_comparison_parser;
      reversed\<leftarrow>xml_bool (STR ''reversed''); a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      xml_return (LPPEComparisonError f comparison reversed a b gs active saved)}) XMLor
    (XMLdo (STR ''checkedFiniteComparison'') {
      evidence\<leftarrow>lpp_finite_comparison_parser;
      yf\<leftarrow>lpp_evaluation_types_parser (STR ''yesTypes'');
      nf\<leftarrow>lpp_evaluation_types_parser (STR ''noTypes'');
      ef\<leftarrow>lpp_evaluation_types_parser (STR ''errorTypes'');
      xml_return (LPPEPrimitive (LPPEComparison evidence yf nf ef))}) XMLor
    (XMLdo (STR ''normalizedFiniteEvaluation'') {
      a\<leftarrow>lpc_term_parser; e\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      result_var\<leftarrow>xml_text (STR ''resultVariable''); middle\<leftarrow>lpc_link_parser;
      fs\<leftarrow>lpp_evaluation_types_parser (STR ''types'');
      xml_return (LPPEFiniteIs a e gs active saved result_var middle fs)}) XMLor
    (XMLdo (STR ''normalizedFiniteLength'') {
      a\<leftarrow>lpc_term_parser; e\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      result_var\<leftarrow>xml_text (STR ''resultVariable''); middle\<leftarrow>lpc_link_parser;
      fs\<leftarrow>lpp_evaluation_types_parser (STR ''types'');
      xml_return (LPPEFiniteLength a e gs active saved result_var middle fs)}) XMLor
    (XMLdo (STR ''subtractLibrary'') {
      e\<leftarrow>lpc_term_parser; s\<leftarrow>lpc_term_parser; a\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      middle\<leftarrow>lpc_link_parser;
      fs\<leftarrow>lpp_evaluation_types_parser (STR ''types'');
      xml_return (LPPESubtractLibrary e s a gs active saved middle fs)}) XMLor
    (XMLdo (STR ''normalizedConstantEvaluation'') {
      evidence\<leftarrow>lpp_integer_expression_parser; a\<leftarrow>lpc_term_parser; e\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      middle\<leftarrow>lpc_link_parser; fs\<leftarrow>lpp_evaluation_types_parser (STR ''types'');
      xml_return (LPPEConstantIs evidence a e gs active saved middle fs)}) XMLor
    (XMLdo (STR ''trimBarriers'') {
      successor\<leftarrow>lpc_return_state_parser; barriers\<leftarrow>lpc_return_state_parser;
      e\<leftarrow>lpc_link_parser; fs\<leftarrow>lpp_evaluation_types_parser (STR ''types'');
      xml_return (LPPETrim successor barriers e fs)}) XMLor
    (XMLdo (STR ''parallelAlternatives'') {
      links\<leftarrow>xml_many (STR ''links'') lpc_link_parser id;
      fs\<leftarrow>xml_many (STR ''linkTypes'') (lpp_evaluation_types_parser (STR ''types'')) id;
      xml_return (LPPEParallel links fs)}) XMLor
    (XMLdo (STR ''refutedContext'') {
      i\<leftarrow>xml_nat (STR ''index''); k\<leftarrow>xml_nat (STR ''refresh'');
      bindings\<leftarrow>lpc_bindings_parser;
      xml_return (LPPERefuted i k bindings)})"

end
