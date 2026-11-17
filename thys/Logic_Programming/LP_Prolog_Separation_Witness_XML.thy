theory LP_Prolog_Separation_Witness_XML
 imports LP_Prolog_Separation_Table_Check LP_Cut_Table_XML
begin

text \<open>Untrusted local evidence only. Parsing does not establish the source
table, initial query, module dependencies, or residual termination.\<close>

definition lpp_separation_fact_parser where
 "lpp_separation_fact_parser = XMLdo (STR ''separate'') {
   a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser; xml_return (LPPSeparate a b)}"

definition lpp_separation_facts_parser where
 "lpp_separation_facts_parser tag = xml_many tag lpp_separation_fact_parser id"

definition lpp_separation_head_parser where
 "lpp_separation_head_parser =
  (XMLdo (STR ''matchingHead'') {bs\<leftarrow>lpc_bindings_parser; xml_return (LPPSMatching bs)}) XMLor
  (XMLdo (STR ''anchoredHead'') {
   f\<leftarrow>xml_singleton (STR ''symbol'') lpc_symbol_parser id;
   ats\<leftarrow>xml_many (STR ''actuals'') lpc_term_parser id;
   hs\<leftarrow>xml_many (STR ''headArgs'') lpc_term_parser id;
   G\<leftarrow>xml_many (STR ''ground'') (xml_text (STR ''var'')) id;
   xml_return (LPPSAnchored f ats hs G)}) XMLor
  (XMLdo (STR ''spineHead'') {
   f\<leftarrow>xml_singleton (STR ''symbol'') lpc_symbol_parser id;
   a\<leftarrow>xml_singleton (STR ''argument'') lpc_term_parser id;
   ats\<leftarrow>xml_many (STR ''actuals'') lpc_term_parser id;
   x\<leftarrow>xml_text (STR ''headVar''); y\<leftarrow>xml_text (STR ''tailVar'');
   H\<leftarrow>xml_many (STR ''others'') (xml_text (STR ''var'')) id;
   xml_return (LPPSSpine f a ats x y H)})"

definition lpp_separation_witness_parser where
 "lpp_separation_witness_parser =
  (XMLdo (STR ''absent'') {xml_return None}) XMLor
  (XMLdo (STR ''ordinary'') {xml_return (Some LPPSOrdinaryAction)}) XMLor
  (XMLdo (STR ''groundEquality'') {xml_return (Some (LPPSUnificationAction None))}) XMLor
  (XMLdo (STR ''head'') {h\<leftarrow>lpp_separation_head_parser;
    xml_return (Some (LPPSUnificationAction (Some h)))}) XMLor
  (XMLdo (STR ''pair'') {xml_return (Some LPPSPairAction)}) XMLor
  (XMLdo (STR ''reflexive'') {
    retained\<leftarrow>lpp_separation_facts_parser (STR ''retained'');
    failed\<leftarrow>lpp_separation_facts_parser (STR ''failed'');
    xml_return (Some (LPPSReflexiveAction retained failed))}) XMLor
  (XMLdo (STR ''fresh'') {
    normalized_facts\<leftarrow>lpp_separation_facts_parser (STR ''normalized'');
    failed\<leftarrow>lpp_separation_facts_parser (STR ''failed'');
    x\<leftarrow>xml_text (STR ''input''); y\<leftarrow>xml_text (STR ''name''); z\<leftarrow>xml_text (STR ''arguments'');
    matching\<leftarrow>lpc_bindings_parser;
    xml_return (Some (LPPSFreshAction normalized_facts failed x y z matching))}) XMLor
  (XMLdo (STR ''univ'') {
    f\<leftarrow>xml_singleton (STR ''symbol'') lpc_symbol_parser id;
    n\<leftarrow>xml_singleton (STR ''name'') lpc_term_parser id;
    ats\<leftarrow>xml_singleton (STR ''arguments'') lpc_term_parser id;
    xml_return (Some (LPPSUnivAction f n ats))})"

definition lpp_separation_witnesses_parser where
 "lpp_separation_witnesses_parser = xml_many (STR ''separationWitnesses'')
   (xml_singleton (STR ''row'') lpp_separation_witness_parser id) id"


definition lpp_decode_separation_witnesses where
 "lpp_decode_separation_witnesses xml = parse_xml_string lpp_separation_witnesses_parser xml"

end
