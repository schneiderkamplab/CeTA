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
    (XMLdo (STR ''identityTest'') {
      f\<leftarrow>xml_text (STR ''predicate''); a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      yes\<leftarrow>lpc_link_parser; no\<leftarrow>lpc_link_parser;
      yf\<leftarrow>lpp_evaluation_types_parser (STR ''yesTypes'');
      nf\<leftarrow>lpp_evaluation_types_parser (STR ''noTypes'');
      xml_return (LPPEPrimitive (LPPEIdentity f a b gs active saved yes no yf nf))}) XMLor
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
