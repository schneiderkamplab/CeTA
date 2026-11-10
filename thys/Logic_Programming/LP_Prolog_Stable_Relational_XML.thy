theory LP_Prolog_Stable_Relational_XML
 imports LP_Prolog_Stable_Mixed_Profile LP_Prolog_Stable_Guarded_XML
begin

definition lpp_relational_component_parser where
  "lpp_relational_component_parser =
    (XMLdo (STR ''existingComponent'') {
      block\<leftarrow>lpp_established_finite_component_parser;
      descent\<leftarrow>lpp_finite_guarded_descent_parser;
      xml_return (fst block,LPPSExisting (snd block) descent)}) XMLor
    (XMLdo (STR ''relationalGroundSplit'') {
      split\<leftarrow>lpc_triple_split_parser;
      evidence\<leftarrow>lpp_finite_ground_receipt_parser;
      first_types\<leftarrow>lpp_evaluation_types_parser (STR ''firstTypes'');
      second_types\<leftarrow>lpp_evaluation_types_parser (STR ''secondTypes'');
      atom\<leftarrow>xml_singleton (STR ''returnedCall'') lpp_success_atom_parser id;
      first_call\<leftarrow>xml_singleton (STR ''firstCall'') lpc_triple_clause_receipt_parser id;
      second_call\<leftarrow>xml_singleton (STR ''secondCall'') lpc_triple_clause_receipt_parser id;
      xml_return (None,LPPSRelational first_types second_types split evidence atom first_call second_call)}) XMLor
    (XMLdo (STR ''relationalShapeSplit'') {
      split\<leftarrow>lpc_triple_split_parser;
      evidence\<leftarrow>lpp_finite_shape_receipt_parser;
      first_types\<leftarrow>lpp_evaluation_types_parser (STR ''firstTypes'');
      second_types\<leftarrow>lpp_evaluation_types_parser (STR ''secondTypes'');
      atom\<leftarrow>xml_singleton (STR ''returnedCall'') lpp_success_atom_parser id;
      first_call\<leftarrow>xml_singleton (STR ''firstCall'') lpc_triple_clause_receipt_parser id;
      second_call\<leftarrow>xml_singleton (STR ''secondCall'') lpc_triple_clause_receipt_parser id;
      xml_return (None,LPPSControlShape first_types second_types split evidence atom first_call second_call)})"

definition lpp_relational_component_header where
  "lpp_relational_component_header P fuel transfer component =
    (case component of (header,LPPSExisting old descent) \<Rightarrow>
      lpp_established_finite_component_header P fuel transfer (header,old)
    | (header,LPPSRelational ft st split evidence atom first_call second_call) \<Rightarrow> header=None
    | (header,LPPSControlShape ft st split evidence atom first_call second_call) \<Rightarrow> header=None)"

definition lpp_structural_entries_parser where
  "lpp_structural_entries_parser = xml_many (STR ''entries'') (XMLdo (STR ''entry'') {
    q\<leftarrow>xml_text (STR ''predicate''); n\<leftarrow>xml_nat (STR ''arity'');
    positions\<leftarrow>xml_many (STR ''ground'') (xml_nat (STR ''index'')) id;
    xml_return (q,n,positions)}) id"

definition lpp_structural_coverage_parser where
  "lpp_structural_coverage_parser = xml_many (STR ''coverage'') (XMLdo (STR ''row'') {
    slot\<leftarrow>xml_nat (STR ''entryIndex'');
    facts\<leftarrow>xml_many (STR ''facts'') lpp_transfer_fact_parser id;
    xml_return (slot,facts)}) id"

text \<open>These parsers preserve local return evidence and both child-call
receipts. Parsing alone establishes no source or component verdict.\<close>
end
