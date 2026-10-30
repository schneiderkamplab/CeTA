theory LP_Prolog_Context_Composed_XML
 imports LP_Prolog_Context_Module_XML LP_Prolog_Context_Composed
begin

definition lpp_context_data_parser where
  "lpp_context_data_parser = XMLdo (STR ''contextModule'') {
    nds\<leftarrow>xml_many (STR ''nodes'') lpc_node_parser id;
    states\<leftarrow>xml_many (STR ''returnStates'') lpc_return_state_parser id;
    contexts\<leftarrow>xml_many (STR ''contexts'') lpp_source_context_parser id;
    typings\<leftarrow>xml_many (STR ''typings'') (xml_many (STR ''facts'') lpp_transfer_fact_parser id) id;
    returned\<leftarrow>xml_singleton (STR ''returnSymbol'') lpc_symbol_parser id;
    arity\<leftarrow>xml_nat (STR ''returnArity'');
    actions\<leftarrow>xml_many (STR ''actions'') lpp_context_module_action_parser id;
    xml_return \<lparr>lppcm_nodes = nds,lppcm_states = states,lppcm_contexts = contexts,
      lppcm_typings = typings,lppcm_returned = returned,lppcm_arity = arity,lppcm_actions = actions\<rparr>}"

definition lpp_context_composed_action_parser where
  "lpp_context_composed_action_parser =
    (xml_change lpp_context_module_action_parser (\<lambda>a. xml_return (LPPCCLocal a))) XMLor
    (XMLdo (STR ''returnSplit'') {
      bindings\<leftarrow>xml_many (STR ''routing'') (xml_pair (STR ''route'') (xml_text (STR ''var'')) (xml_nat (STR ''index'')) Pair) id;
      indices\<leftarrow>xml_many (STR ''projection'') (xml_nat (STR ''index'')) id;
      pre\<leftarrow>xml_many (STR ''prefix'') lpc_goal_parser id;
      rest\<leftarrow>xml_many (STR ''continuation'') lpc_goal_parser id;
      interface\<leftarrow>xml_many (STR ''interface'') lpc_term_parser id;
      pm\<leftarrow>lpp_context_data_parser; pe\<leftarrow>lpc_link_parser;
      vs\<leftarrow>xml_many (STR ''returnVariables'') (xml_text (STR ''var'')) id;
      cm\<leftarrow>lpp_context_data_parser; ce\<leftarrow>lpc_link_parser;
      xml_return (LPPCCSplit bindings indices pre rest interface pm pe vs cm ce)})"

definition lpp_context_composed_parser where
  "lpp_context_composed_parser = XMLdo (STR ''prologContextComposed'') {
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,bs)}) id;
    fuel\<leftarrow>xml_nat (STR ''fuel''); r\<leftarrow>xml_nat (STR ''root'');
    nds\<leftarrow>xml_many (STR ''nodes'') lpc_node_parser id;
    states\<leftarrow>xml_many (STR ''returnStates'') lpc_return_state_parser id;
    contexts\<leftarrow>xml_many (STR ''contexts'') lpp_source_context_parser id;
    typings\<leftarrow>xml_many (STR ''typings'') (xml_many (STR ''facts'') lpp_transfer_fact_parser id) id;
    transfer\<leftarrow>lpp_transfer_contract_parser;
    returned\<leftarrow>xml_singleton (STR ''returnSymbol'') lpc_symbol_parser id;
    arity\<leftarrow>xml_nat (STR ''returnArity'');
    actions\<leftarrow>xml_many (STR ''actions'') lpp_context_composed_action_parser id;
    Q\<leftarrow>xml_many (STR ''residual'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
    xml_return (P,fuel,r,nds,states,contexts,typings,transfer,returned,arity,actions,Q)}"

end
