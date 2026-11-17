theory LP_Prolog_Separation_State_XML
 imports LP_Prolog_Separation_Witness_XML LP_Prolog_Context_Module_XML
begin

text \<open>Complete state arrays for the premised table checker. Decoding alone
establishes neither context initialization nor a module boundary contract.\<close>

definition lpp_separation_functor_parser where
 "lpp_separation_functor_parser = XMLdo (STR ''functor'') {
   t\<leftarrow>lpc_term_parser; n\<leftarrow>lpc_term_parser; ats\<leftarrow>lpc_term_parser;
   xml_return (LPPFunctorFact t n ats)}"

definition lpp_separation_states_parser where
 "lpp_separation_states_parser = XMLdo (STR ''separationStates'') {
   nds\<leftarrow>xml_many (STR ''nodes'') lpc_node_parser id;
   states\<leftarrow>xml_many (STR ''returnStates'') lpc_return_state_parser id;
   contexts\<leftarrow>xml_many (STR ''contexts'') lpp_source_context_parser id;
   frees\<leftarrow>xml_many (STR ''freeContexts'')
     (xml_many (STR ''free'') (xml_text (STR ''var'')) id) id;
   functors\<leftarrow>xml_many (STR ''functorContexts'')
     (xml_many (STR ''functors'') lpp_separation_functor_parser id) id;
   separations\<leftarrow>xml_many (STR ''separationContexts'')
     (lpp_separation_facts_parser (STR ''separation'')) id;
   returned\<leftarrow>xml_singleton (STR ''returnSymbol'') lpc_symbol_parser id;
   arity\<leftarrow>xml_nat (STR ''returnArity'');
   xml_return (nds,states,contexts,frees,functors,separations,returned,arity)}"

definition lpp_decode_separation_states where
 "lpp_decode_separation_states xml = parse_xml_string lpp_separation_states_parser xml"

end
