theory LP_Prolog_Context_XML
  imports LP_Prolog_Context_Query LP_Prolog_Success_Transfer_XML LP_Prolog_Numeric_Row_XML
begin

definition lpp_source_context_parser where
  "lpp_source_context_parser = XMLdo (STR ''sourceContext'') {
    facts\<leftarrow>xml_many (STR ''facts'') lpp_success_atom_parser id;
    guards\<leftarrow>xml_many (STR ''guards'') lpp_success_guard_parser id;
    observations\<leftarrow>xml_many (STR ''observations'')
      ((xml_singleton (STR ''integerGuard'') lpc_term_parser LPPOInteger) XMLor lpp_numeric_observation_parser) id;
    xml_return (facts,guards,observations)}"

definition lpp_integer_return_action_parser where
  "lpp_integer_return_action_parser =
    (xml_singleton (STR ''cut'') lpc_return_action_parser LPPIRCut) XMLor
    (XMLdo (STR ''integerTest'') {
      a\<leftarrow>lpc_term_parser; gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      yes\<leftarrow>lpc_link_parser; no\<leftarrow>lpc_link_parser;
      xml_return (LPPIRTest a gs active saved yes no)}) XMLor
    (XMLdo (STR ''integerComparison'') {
      K\<leftarrow>xml_many (STR ''known'') (xml_text (STR ''var'')) id;
      f\<leftarrow>xml_text (STR ''predicate''); comparison\<leftarrow>lpp_numeric_comparison_parser;
      reversed\<leftarrow>xml_bool (STR ''reversed''); a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser;
      ea\<leftarrow>lpp_integer_expression_parser; eb\<leftarrow>lpp_integer_expression_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      yes\<leftarrow>lpc_link_parser; no\<leftarrow>lpc_link_parser;
      xml_return (LPPIRCompare K f comparison reversed a b ea eb gs active saved yes no)}) XMLor
    (XMLdo (STR ''integerEvaluation'') {
      K\<leftarrow>xml_many (STR ''known'') (xml_text (STR ''var'')) id;
      evidence\<leftarrow>lpp_integer_expression_parser; a\<leftarrow>lpc_term_parser; e\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      result_var\<leftarrow>xml_text (STR ''resultVariable'');
      k\<leftarrow>xml_nat (STR ''activePrefix''); l\<leftarrow>xml_nat (STR ''clausePrefix'');
      continuation\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id; mode\<leftarrow>lpc_mode_parser;
      outputs\<leftarrow>xml_many (STR ''outputs'') lpc_term_parser id;
      yes\<leftarrow>lpc_link_parser; no\<leftarrow>lpc_link_parser;
      xml_return (LPPIRIs K evidence a e gs active saved result_var k l continuation mode outputs yes no)})"

definition lpp_context_source_action_parser where
  "lpp_context_source_action_parser =
    (xml_change lpp_integer_return_action_parser (xml_return o LPPCSPrimitive)) XMLor
    (XMLdo (STR ''stagedIntegerEvaluation'') {
      K\<leftarrow>xml_many (STR ''known'') (xml_text (STR ''var'')) id;
      evidence\<leftarrow>lpp_integer_expression_parser; a\<leftarrow>lpc_term_parser; e\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      result_var\<leftarrow>xml_text (STR ''resultVariable''); middle\<leftarrow>lpc_link_parser;
      action\<leftarrow>lpc_return_action_parser;
      xml_return (LPPCSStagedIs K evidence a e gs active saved result_var middle action)}) XMLor
    (XMLdo (STR ''constantIntegerEvaluation'') {
      evidence\<leftarrow>lpp_integer_expression_parser; a\<leftarrow>lpc_term_parser; e\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      middle\<leftarrow>lpc_link_parser; action\<leftarrow>lpc_return_action_parser;
      xml_return (LPPCSConstantIs evidence a e gs active saved middle action)}) XMLor
    (XMLdo (STR ''identityTest'') {
      f\<leftarrow>xml_text (STR ''predicate''); a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id; saved\<leftarrow>lpc_return_state_parser;
      yes\<leftarrow>lpc_link_parser; no\<leftarrow>lpc_link_parser;
      xml_return (LPPCSIdentity f a b gs active saved yes no)})"

text \<open>The table parser is shared by the source envelope. Checking a table
alone is diagnostic: residual termination and the queried source remain
mandatory premises and cannot be replaced by this endpoint.\<close>
definition lpp_context_table_parser where
  "lpp_context_table_parser = XMLdo (STR ''prologContextTable'') {
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
    actions\<leftarrow>xml_many (STR ''actions'') lpp_context_source_action_parser id;
    Q\<leftarrow>xml_many (STR ''residual'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
    xml_return (P,fuel,r,nds,states,contexts,typings,transfer,returned,arity,actions,Q)}"

definition check_lpp_context_table_xml where
  "check_lpp_context_table_xml xml = (case parse_xml_string lpp_context_table_parser xml of
    Right (P,fuel,r,nds,states,contexts,typings,(summaries,SP,receipts),returned,arity,actions,Q) \<Rightarrow>
      lp_cut_source_program P \<and> lpp_check_transfer_contract summaries SP receipts \<and>
      lpp_check_context_root fuel P Q nds states contexts (lpp_transfer_lookup summaries) typings returned arity actions r
    | _ \<Rightarrow> False)"

theorem check_lpp_context_table_xml_sound:
  assumes parsed: "parse_xml_string lpp_context_table_parser xml =
    Right (P,fuel,r,nds,states,contexts,typings,(summaries,SP,receipts),returned,arity,actions,Q)"
    and checked: "check_lpp_context_table_xml xml"
    and known: "lp_cut_knowledge (set (lpcn_ground (nds!r))) (lpcn_guards (nds!r)) eta"
    and residual: "SN_on (lp_ild Q) {[(lpcn_pred (nds!r),map eta (lpcn_vars (nds!r)))]}"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    {map fst (lpc_return_eval eta (states!r))}"
  by (rule lpp_context_root_domain_SN[OF _ _ _ known residual])
    (use parsed checked in \<open>auto simp: check_lpp_context_table_xml_def lpp_check_transfer_contract_def\<close>)
end
