theory LP_Prolog_Separation_Action_XML
 imports LP_Prolog_Separation_Link_XML
begin

definition lpp_separation_transfer_facts_parser where
 "lpp_separation_transfer_facts_parser tag = xml_many tag lpp_transfer_fact_parser id"

definition lpp_separation_action_parser where
 "lpp_separation_action_parser =
  (XMLdo (STR ''absent'') {xml_return None}) XMLor
  (XMLdo (STR ''cut'') {a\<leftarrow>lpc_return_action_parser;
    yes\<leftarrow>lpp_separation_transfer_facts_parser (STR ''yesFacts'');
    no\<leftarrow>lpp_separation_transfer_facts_parser (STR ''noFacts'');
    xml_return (Some (LPPFCut a yes no))}) XMLor
  (XMLdo (STR ''test'') {yes\<leftarrow>lpc_link_parser; no\<leftarrow>lpc_link_parser;
    yf\<leftarrow>lpp_separation_transfer_facts_parser (STR ''yesFacts'');
    nf\<leftarrow>lpp_separation_transfer_facts_parser (STR ''noFacts'');
    xml_return (Some (LPPFTest yes no yf nf))}) XMLor
  (XMLdo (STR ''observedIs'') {v\<leftarrow>xml_text (STR ''resultVariable'');
    e\<leftarrow>lpc_link_parser; fs\<leftarrow>lpp_separation_transfer_facts_parser (STR ''facts'');
    xml_return (Some (LPPFIs v e fs))}) XMLor
  (XMLdo (STR ''univ'') {v\<leftarrow>xml_text (STR ''valueVariable'');
    n\<leftarrow>xml_text (STR ''nameVariable''); a\<leftarrow>xml_text (STR ''argumentsVariable'');
    e\<leftarrow>lpc_link_parser; fs\<leftarrow>lpp_separation_transfer_facts_parser (STR ''facts'');
    xml_return (Some (LPPFUniv v n a e fs))}) XMLor
  (XMLdo (STR ''trim'') {ss\<leftarrow>lpc_return_state_parser; bs\<leftarrow>lpc_return_state_parser;
    e\<leftarrow>lpc_link_parser; fs\<leftarrow>lpp_separation_transfer_facts_parser (STR ''facts'');
    xml_return (Some (LPPFTrim ss bs e fs))}) XMLor
  (XMLdo (STR ''parallel'') {es\<leftarrow>xml_many (STR ''links'') lpc_link_parser id;
    fs\<leftarrow>xml_many (STR ''factRows'') (lpp_separation_transfer_facts_parser (STR ''facts'')) id;
    xml_return (Some (LPPFParallel es fs))})"

definition lpp_separation_actions_parser where
 "lpp_separation_actions_parser = xml_many (STR ''separationActions'') lpp_separation_action_parser id"

definition lpp_decode_separation_actions where
 "lpp_decode_separation_actions xml = parse_xml_string lpp_separation_actions_parser xml"

end
