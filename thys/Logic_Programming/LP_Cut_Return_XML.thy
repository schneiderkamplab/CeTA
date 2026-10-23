theory LP_Cut_Return_XML
  imports LP_Cut_Table_XML LP_Cut_Return_Certificate
begin

definition lpc_return_state_parser where
  "lpc_return_state_parser = xml_many (STR ''returnState'')
    (XMLdo (STR ''frame'') {e\<leftarrow>lpc_entry_parser;
      ts\<leftarrow>xml_many (STR ''outputs'') lpc_term_parser id;
      xml_return (e,ts)}) id"

definition lpc_return_event_parser where
  "lpc_return_event_parser =
    (XMLdo (STR ''silent'') {xml_return None}) XMLor
    (xml_change (xml_many (STR ''returned'') lpc_term_parser id)
      (\<lambda>ts. xml_return (Some ts)))"

definition lpc_return_action_parser where
  "lpc_return_action_parser =
    (XMLdo (STR ''terminal'') {xml_return LPCRTerminal}) XMLor
    (XMLdo (STR ''inconsistent'') {xml_return LPCRInconsistent}) XMLor
    (XMLdo (STR ''admin'') {event\<leftarrow>lpc_return_event_parser;
      ss\<leftarrow>lpc_return_state_parser; e\<leftarrow>lpc_link_parser;
      xml_return (LPCRAdmin event ss e)}) XMLor
    (XMLdo (STR ''allocate'') {m\<leftarrow>xml_nat (STR ''scope'');
      f\<leftarrow>xml_text (STR ''predicate'');
      ts\<leftarrow>xml_many (STR ''arguments'') lpc_term_parser id;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id;
      saved\<leftarrow>lpc_return_state_parser; e\<leftarrow>lpc_link_parser;
      xml_return (LPCRCase m f ts gs active saved e)}) XMLor
    (XMLdo (STR ''metaCall'') {m\<leftarrow>xml_nat (STR ''scope'');
      a\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id;
      saved\<leftarrow>lpc_return_state_parser;
      body\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id;
      e\<leftarrow>lpc_link_parser;
      xml_return (LPCRMeta m a gs active saved body e)}) XMLor
    (XMLdo (STR ''equality'') {a\<leftarrow>lpc_term_parser; b\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id;
      saved\<leftarrow>lpc_return_state_parser;
      k\<leftarrow>xml_nat (STR ''activePrefix''); l\<leftarrow>xml_nat (STR ''clausePrefix'');
      successor\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      mode\<leftarrow>lpc_mode_parser;
      outputs\<leftarrow>xml_many (STR ''outputs'') lpc_term_parser id;
      yes\<leftarrow>lpc_link_parser; no\<leftarrow>lpc_link_parser;
      xml_return (LPCREquality a b gs active saved k l successor mode outputs yes no)}) XMLor
    (XMLdo (STR ''resolve'') {a\<leftarrow>lpc_term_parser;
      gs\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      c\<leftarrow>xml_nat (STR ''index''); m\<leftarrow>xml_nat (STR ''scope'');
      active\<leftarrow>xml_many (STR ''active'') lpc_term_parser id;
      saved\<leftarrow>lpc_return_state_parser;
      k\<leftarrow>xml_nat (STR ''activePrefix''); l\<leftarrow>xml_nat (STR ''clausePrefix'');
      A\<leftarrow>xml_many (STR ''anchors'') (xml_text (STR ''var'')) id;
      successor\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
      anchors\<leftarrow>xml_many (STR ''anchorTerms'') lpc_term_parser id;
      bindings\<leftarrow>lpc_bindings_parser; mode\<leftarrow>lpc_mode_parser;
      outputs\<leftarrow>xml_many (STR ''outputs'') lpc_term_parser id;
      yes\<leftarrow>lpc_link_parser; no\<leftarrow>lpc_link_parser;
      xml_return (LPCRResolution a gs c m active saved k l A successor anchors bindings mode outputs yes no)})"

definition lpc_return_constructor_parser where
  "lpc_return_constructor_parser = XMLdo (STR ''lpCutReturnConstructorGraphTerminationProof'') {
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,bs)}) id;
    q\<leftarrow>xml_text (STR ''predicate'');
    modes\<leftarrow>xml_many (STR ''modes'') (xml_bool (STR ''mode'')) id;
    fuel\<leftarrow>xml_nat (STR ''fuel''); r\<leftarrow>xml_nat (STR ''root'');
    nds\<leftarrow>xml_many (STR ''nodes'') lpc_node_parser id;
    states\<leftarrow>xml_many (STR ''returnStates'') lpc_return_state_parser id;
    returned\<leftarrow>xml_singleton (STR ''returnSymbol'') lpc_symbol_parser id;
    arity\<leftarrow>xml_nat (STR ''returnArity'');
    acts\<leftarrow>xml_many (STR ''actions'') lpc_return_action_parser id;
    Q\<leftarrow>xml_many (STR ''residual'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
    enc_pred\<leftarrow>xml_many (STR ''predicateEncoding'') (xml_pair (STR ''encoding'') lpc_symbol_parser symbol_parser Pair) id;
    enc_data\<leftarrow>xml_many (STR ''dataEncoding'') (xml_pair (STR ''encoding'') lpc_symbol_parser symbol_parser Pair) id;
    child\<leftarrow>lp_constructor_parser;
    xml_return (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,child)
  }"

text \<open>Diagnostic endpoint for independently checking local return tables.
It is deliberately not a termination verdict: no residual termination premise
is discharged here.\<close>
definition lpc_return_table_parser where
  "lpc_return_table_parser = XMLdo (STR ''lpCutReturnTable'') {
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,bs)}) id;
    fuel\<leftarrow>xml_nat (STR ''fuel'');
    nds\<leftarrow>xml_many (STR ''nodes'') lpc_node_parser id;
    states\<leftarrow>xml_many (STR ''returnStates'') lpc_return_state_parser id;
    returned\<leftarrow>xml_singleton (STR ''returnSymbol'') lpc_symbol_parser id;
    arity\<leftarrow>xml_nat (STR ''returnArity'');
    acts\<leftarrow>xml_many (STR ''actions'') lpc_return_action_parser id;
    Q\<leftarrow>xml_many (STR ''residual'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
    xml_return (P,fuel,nds,states,returned,arity,acts,Q)
  }"

definition check_lpc_return_table_xml where
  "check_lpc_return_table_xml xml = (case parse_xml_string lpc_return_table_parser xml of
    Right (P,fuel,nds,states,returned,arity,acts,Q) \<Rightarrow>
      lpc_check_return_table fuel P Q nds states returned arity acts
    | _ \<Rightarrow> False)"

definition check_lpc_return_constructor_xml where
  "check_lpc_return_constructor_xml xml = (case parse_xml_string lpc_return_constructor_parser xml of
    Right (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))\<Rightarrow>
      check_lpc_return_constructor tp_rbt_impl dpp_rbt_impl fuel P Q nds states returned arity acts r q modes enc_pred enc_data
        R outs fallback names marks filters q' n positions seed nfs prf
    | _\<Rightarrow>False)"

theorem check_lpc_return_constructor_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpc_return_constructor_parser xml =
    Right (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))"
    and ok: "check_lpc_return_constructor_xml xml" and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_cut_mgu_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  by (rule check_lpc_return_constructor_sound[OF tp_rbt_impl dpp_rbt_impl _ len ground])
    (use parsed ok in \<open>simp add: check_lpc_return_constructor_xml_def\<close>)

end
