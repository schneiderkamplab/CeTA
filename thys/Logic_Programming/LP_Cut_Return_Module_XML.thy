theory LP_Cut_Return_Module_XML
  imports LP_Cut_Return_XML LP_Cut_Return_Module_Certificate
begin

definition lpc_return_module_action_parser where
  "lpc_return_module_action_parser =
    (xml_change lpc_return_action_parser (\<lambda>a. xml_return (LPCRPrimitive a))) XMLor
    (XMLdo (STR ''trimBarriers'') {successor\<leftarrow>lpc_return_state_parser;
      barriers\<leftarrow>lpc_return_state_parser; e\<leftarrow>lpc_link_parser;
      xml_return (LPCRTrim successor barriers e)}) XMLor
    (XMLdo (STR ''parallelAlternatives'') {links\<leftarrow>xml_many (STR ''links'') lpc_link_parser id;
      xml_return (LPCRParallel links)}) XMLor
    (XMLdo (STR ''refutedGuard'') {i\<leftarrow>xml_nat (STR ''index''); k\<leftarrow>xml_nat (STR ''prefix'');
      bindings\<leftarrow>lpc_bindings_parser; xml_return (LPCRRefuted i k bindings)})"

definition lpc_return_module_constructor_parser where
  "lpc_return_module_constructor_parser = XMLdo (STR ''lpCutReturnModuleConstructorGraphTerminationProof'') {
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
    acts\<leftarrow>xml_many (STR ''actions'') lpc_return_module_action_parser id;
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
definition lpc_return_module_table_parser where
  "lpc_return_module_table_parser = XMLdo (STR ''lpCutReturnModuleTable'') {
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,bs)}) id;
    fuel\<leftarrow>xml_nat (STR ''fuel'');
    nds\<leftarrow>xml_many (STR ''nodes'') lpc_node_parser id;
    states\<leftarrow>xml_many (STR ''returnStates'') lpc_return_state_parser id;
    returned\<leftarrow>xml_singleton (STR ''returnSymbol'') lpc_symbol_parser id;
    arity\<leftarrow>xml_nat (STR ''returnArity'');
    acts\<leftarrow>xml_many (STR ''actions'') lpc_return_module_action_parser id;
    Q\<leftarrow>xml_many (STR ''residual'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
    xml_return (P,fuel,nds,states,returned,arity,acts,Q)
  }"

definition check_lpc_return_module_table_xml where
  "check_lpc_return_module_table_xml xml = (case parse_xml_string lpc_return_module_table_parser xml of
    Right (P,fuel,nds,states,returned,arity,acts,Q) \<Rightarrow>
      lpc_check_return_module fuel P Q nds states returned arity acts
    | _ \<Rightarrow> False)"

definition check_lpc_return_module_constructor_xml where
  "check_lpc_return_module_constructor_xml xml = (case parse_xml_string lpc_return_module_constructor_parser xml of
    Right (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))\<Rightarrow>
      check_lpc_return_module_constructor tp_rbt_impl dpp_rbt_impl fuel P Q nds states returned arity acts r q modes enc_pred enc_data
        R outs fallback names marks filters q' n positions seed nfs prf
    | _\<Rightarrow>False)"

theorem check_lpc_return_module_constructor_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpc_return_module_constructor_parser xml =
    Right (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (R,outs,fallback,names,marks,filters,(q',n,positions),seed,nfs,prf))"
    and ok: "check_lpc_return_module_constructor_xml xml" and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_cut_mgu_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  by (rule check_lpc_return_module_constructor_sound[OF tp_rbt_impl dpp_rbt_impl _ len ground])
    (use parsed ok in \<open>simp add: check_lpc_return_module_constructor_xml_def\<close>)

end

