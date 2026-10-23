theory LP_Cut_Return_Composed_XML
  imports LP_Cut_Return_Module_XML LP_Cut_Return_Composed_Certificate
begin

definition lpc_return_module_data_parser where
  "lpc_return_module_data_parser = XMLdo (STR ''returnModule'') {
    nds\<leftarrow>xml_many (STR ''nodes'') lpc_node_parser id;
    states\<leftarrow>xml_many (STR ''returnStates'') lpc_return_state_parser id;
    returned\<leftarrow>xml_singleton (STR ''returnSymbol'') lpc_symbol_parser id;
    arity\<leftarrow>xml_nat (STR ''returnArity'');
    acts\<leftarrow>xml_many (STR ''actions'') lpc_return_module_action_parser id;
    xml_return \<lparr>lpcrm_nodes=nds,lpcrm_states=states,lpcrm_returned=returned,
      lpcrm_arity=arity,lpcrm_actions=acts\<rparr>}"

definition lpc_return_composed_action_parser where
  "lpc_return_composed_action_parser =
    (xml_change lpc_return_module_action_parser (\<lambda>a. xml_return (LPCRLocal a))) XMLor
    (XMLdo (STR ''returnSplit'') {
      bindings\<leftarrow>xml_many (STR ''routing'') (xml_pair (STR ''route'') (xml_text (STR ''var'')) (xml_nat (STR ''index'')) Pair) id;
      indices\<leftarrow>xml_many (STR ''projection'') (xml_nat (STR ''index'')) id;
      pre\<leftarrow>xml_many (STR ''prefix'') lpc_goal_parser id;
      rest\<leftarrow>xml_many (STR ''continuation'') lpc_goal_parser id;
      interface\<leftarrow>xml_many (STR ''interface'') lpc_term_parser id;
      prefix_module\<leftarrow>lpc_return_module_data_parser;
      prefix_link\<leftarrow>lpc_link_parser;
      vs\<leftarrow>xml_many (STR ''returnVariables'') (xml_text (STR ''var'')) id;
      continuation_module\<leftarrow>lpc_return_module_data_parser;
      continuation_link\<leftarrow>lpc_link_parser;
      xml_return (LPCRSplit bindings indices pre rest interface prefix_module prefix_link vs continuation_module continuation_link)}) XMLor
    (XMLdo (STR ''groundReturnSplit'') {
      bindings\<leftarrow>xml_many (STR ''routing'') (xml_pair (STR ''route'') (xml_text (STR ''var'')) (xml_nat (STR ''index'')) Pair) id;
      indices\<leftarrow>xml_many (STR ''projection'') (xml_nat (STR ''index'')) id;
      pre\<leftarrow>xml_many (STR ''prefix'') lpc_goal_parser id;
      rest\<leftarrow>xml_many (STR ''continuation'') lpc_goal_parser id;
      interface\<leftarrow>xml_many (STR ''interface'') lpc_term_parser id;
      prefix_module\<leftarrow>lpc_return_module_data_parser;
      prefix_link\<leftarrow>lpc_link_parser;
      vs\<leftarrow>xml_many (STR ''returnVariables'') (xml_text (STR ''var'')) id;
      continuation_module\<leftarrow>lpc_return_module_data_parser;
      continuation_link\<leftarrow>lpc_link_parser;
      positions\<leftarrow>xml_many (STR ''groundPositions'') (xml_nat (STR ''position'')) id;
      groundQ\<leftarrow>xml_many (STR ''groundProgram'') (XMLdo (STR ''clause'') {
        h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
        bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
      Fs\<leftarrow>xml_many (STR ''predicates'') (xml_text (STR ''predicate'')) id;
      modes\<leftarrow>xml_many (STR ''groundModes'') (XMLdo (STR ''groundMode'') {
        f\<leftarrow>xml_singleton (STR ''symbol'') lpc_symbol_parser id;
        n\<leftarrow>xml_nat (STR ''arity'');
        pins\<leftarrow>xml_many (STR ''inputs'') (xml_nat (STR ''position'')) id;
        pouts\<leftarrow>xml_many (STR ''outputs'') (xml_nat (STR ''position'')) id;
        xml_return (LPGroundMode f n pins pouts)}) id;
      xml_return (LPCRGroundSplit bindings indices pre rest interface prefix_module prefix_link vs continuation_module continuation_link positions groundQ Fs modes)})"

definition lpc_return_composed_constructor_parser where
  "lpc_return_composed_constructor_parser = XMLdo (STR ''lpCutReturnComposedConstructorGraphTerminationProof'') {
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
    acts\<leftarrow>xml_many (STR ''actions'') lpc_return_composed_action_parser id;
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
definition lpc_return_composed_table_parser where
  "lpc_return_composed_table_parser = XMLdo (STR ''lpCutReturnComposedTable'') {
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,bs)}) id;
    fuel\<leftarrow>xml_nat (STR ''fuel'');
    nds\<leftarrow>xml_many (STR ''nodes'') lpc_node_parser id;
    states\<leftarrow>xml_many (STR ''returnStates'') lpc_return_state_parser id;
    returned\<leftarrow>xml_singleton (STR ''returnSymbol'') lpc_symbol_parser id;
    arity\<leftarrow>xml_nat (STR ''returnArity'');
    acts\<leftarrow>xml_many (STR ''actions'') lpc_return_composed_action_parser id;
    Q\<leftarrow>xml_many (STR ''residual'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
    xml_return (P,fuel,nds,states,returned,arity,acts,Q)
  }"

definition check_lpc_return_composed_table_xml where
  "check_lpc_return_composed_table_xml xml = (case parse_xml_string lpc_return_composed_table_parser xml of
    Right (P,fuel,nds,states,returned,arity,acts,Q) \<Rightarrow>
      lpc_check_return_composed fuel P Q nds states returned arity acts
    | _ \<Rightarrow> False)"

definition check_lpc_return_composed_constructor_xml where
  "check_lpc_return_composed_constructor_xml xml = (case parse_xml_string lpc_return_composed_constructor_parser xml of
    Right (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))\<Rightarrow>
      check_lpc_return_composed_constructor tp_rbt_impl dpp_rbt_impl fuel P Q nds states returned arity acts r q modes enc_pred enc_data
        R outs fallback names marks filters q' n positions seed nfs prf
    | _\<Rightarrow>False)"

theorem check_lpc_return_composed_constructor_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpc_return_composed_constructor_parser xml =
    Right (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))"
    and ok: "check_lpc_return_composed_constructor_xml xml" and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_cut_mgu_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  by (rule check_lpc_return_composed_constructor_sound[OF tp_rbt_impl dpp_rbt_impl _ len ground])
    (use parsed ok in \<open>simp add: check_lpc_return_composed_constructor_xml_def\<close>)

end


