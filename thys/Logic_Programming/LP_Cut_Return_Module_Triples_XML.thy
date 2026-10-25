theory LP_Cut_Return_Module_Triples_XML
  imports LP_Cut_Return_Module_XML LP_Cut_Return_Module_Triples LP_Dependency_Triple_XML
begin

definition lpc_return_module_triples_parser where
  "lpc_return_module_triples_parser = XMLdo (STR ''lpCutReturnModuleDependencyTriplesProof'') {
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
    child\<leftarrow>lp_triple_pidp_parser;
    xml_return (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,child)
  }"


definition check_lpc_return_module_triples_xml where
  "check_lpc_return_module_triples_xml xml = (case parse_xml_string lpc_return_module_triples_parser xml of
    Right (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (D,R,outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs))\<Rightarrow>
      check_lpc_return_module_triples tp_rbt_impl dpp_rbt_impl fuel P Q nds states returned arity acts r q modes enc_pred enc_data
        D R outs fallback dnames pnames marks filters q' n positions labs proofs
    | _\<Rightarrow>False)"

theorem check_lpc_return_module_triples_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpc_return_module_triples_parser xml =
    Right (P,q,modes,fuel,r,nds,states,returned,arity,acts,Q,enc_pred,enc_data,
      (D,R,outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs))"
    and ok: "check_lpc_return_module_triples_xml xml" and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_cut_mgu_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  by (rule check_lpc_return_module_triples_sound[OF tp_rbt_impl dpp_rbt_impl _ len ground])
    (use parsed ok in \<open>simp add: check_lpc_return_module_triples_xml_def\<close>)

end
