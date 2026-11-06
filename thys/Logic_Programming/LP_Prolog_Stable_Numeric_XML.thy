theory LP_Prolog_Stable_Numeric_XML
  imports LP_Prolog_Stable_Profile_Graph LP_Prolog_Numeric_Component_XML
    LP_Prolog_Stable_Numeric_Code_Setup
begin

definition lpp_stable_coordinate_parser where
  "lpp_stable_coordinate_parser =
    (XMLdo (STR ''integerCoordinate'') {xml_return LPPStableInteger}) XMLor
    (XMLdo (STR ''upperBoundCoordinate'') {xml_return LPPStableUpperBound})"

definition lpp_stable_endpoint_parser where
  "lpp_stable_endpoint_parser = XMLdo (STR ''endpoint'') {
    coordinate\<leftarrow>xml_text (STR ''coordinate'');
    t\<leftarrow>lpc_term_parser;
    e\<leftarrow>(xml_singleton (STR ''integerEndpoint'') lpp_integer_expression_parser LPPStableEndpointInteger)
      XMLor (xml_singleton (STR ''boundEndpoint'') lpc_term_parser LPPStableEndpointBound);
    xml_return (coordinate,t,e)}"

definition lpp_stable_condition_parser where
  "lpp_stable_condition_parser =
    (XMLdo (STR ''integerCondition'') {
      comparison\<leftarrow>lpp_numeric_comparison_parser;
      a\<leftarrow>lpp_integer_expression_parser; b\<leftarrow>lpp_integer_expression_parser;
      xml_return (LPPStableIntegerCondition (comparison,a,b))}) XMLor
    (XMLdo (STR ''upperCondition'') {
      e\<leftarrow>lpp_integer_expression_parser; t\<leftarrow>lpc_term_parser;
      xml_return (LPPStableUpperCondition e t)})"

definition lpp_stable_numeric_key_parser where
  "lpp_stable_numeric_key_parser =
    (xml_change (xml_text (STR ''integerKey'')) (\<lambda>x. xml_return (LPPIntegerKey x))) XMLor
    (xml_singleton (STR ''boundKey'') lpc_term_parser LPPBoundKey)"

definition lpp_stable_numeric_receipt_parser where
  "lpp_stable_numeric_receipt_parser = XMLdo (STR ''row'') {
    facts\<leftarrow>xml_many (STR ''facts'') lpp_transfer_fact_parser id;
    G\<leftarrow>xml_many (STR ''ground'') (xml_text (STR ''var'')) id;
    inputs\<leftarrow>xml_many (STR ''inputs'') lpp_stable_endpoint_parser id;
    outputs\<leftarrow>xml_many (STR ''outputs'') lpp_stable_endpoint_parser id;
    tests\<leftarrow>xml_many (STR ''tests'') lpp_stable_condition_parser id;
    bindings\<leftarrow>xml_many (STR ''bindings'') (XMLdo (STR ''binding'') {
      x\<leftarrow>lpp_stable_numeric_key_parser; v\<leftarrow>trans_var_parser;
      xml_return (x,v)}) id;
    formula\<leftarrow>xml_singleton (STR ''formula'') (formula_parser lpp_numeric_tatom_parser) id;
    xml_return \<lparr>lppsnc_facts = facts,lppsnc_ground = G,lppsnc_inputs = inputs,
      lppsnc_outputs = outputs,lppsnc_tests = tests,lppsnc_bindings = bindings,lppsnc_formula = formula\<rparr>}"

definition lpp_stable_numeric_component_parser where
  "lpp_stable_numeric_component_parser = XMLdo (STR ''prologStableNumericComponent'') {
    transfer\<leftarrow>lpp_transfer_contract_parser;
    coordinates\<leftarrow>xml_many (STR ''coordinates'') (XMLdo (STR ''entry'') {
      p\<leftarrow>xml_text (STR ''predicate'');
      vs\<leftarrow>xml_many (STR ''names'') (xml_text (STR ''coordinate'')) id;
      xml_return (p,vs)}) id;
    coordinate_modes\<leftarrow>xml_many (STR ''coordinateModes'') (XMLdo (STR ''entry'') {
      p\<leftarrow>xml_text (STR ''predicate'');
      ms\<leftarrow>xml_many (STR ''modes'') lpp_stable_coordinate_parser id;
      xml_return (p,ms)}) id;
    locations\<leftarrow>xml_many (STR ''locations'') (XMLdo (STR ''entry'') {
      p\<leftarrow>xml_text (STR ''predicate''); loc\<leftarrow>xml_text (STR ''locationId'');
      xml_return (p,loc)}) id;
    triples\<leftarrow>xml_many (STR ''triples'') lpp_observed_triple_parser id;
    rows\<leftarrow>xml_many (STR ''rows'') lpp_stable_numeric_receipt_parser id;
    system_impl\<leftarrow>ia4_lts_input_parser;
    child_proof\<leftarrow>xml_singleton (STR ''ltsTerminationProof'')
      (ia4_lts_termination_proof_parser :: (ia4_sig,string,IA.ty,string,string,la_solver_type) termination_proof xmlt) id;
    xml_return (transfer,coordinates,coordinate_modes,locations,triples,rows,system_impl,child_proof)}"

text \<open>The parser has no arithmetic-operation witness. All endpoint roles,
ground and type facts, condition receipts, and child dependencies are checked
by the established source assembly. A parsed component alone is not a source
termination result.\<close>
end
