theory LP_Cut_Return_Nested_Triples_XML
  imports LP_Cut_Return_Nested_XML LP_Cut_Return_Nested_Triples LP_Dependency_Triple_XML
begin

definition lpc_return_nested_triples_parser where
  "lpc_return_nested_triples_parser = XMLdo (STR ''lpCutReturnNestedDependencyTriplesProof'') {
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,bs)}) id;
    q\<leftarrow>xml_text (STR ''predicate'');
    modes\<leftarrow>xml_many (STR ''modes'') (xml_bool (STR ''mode'')) id;
    fuel\<leftarrow>xml_nat (STR ''fuel''); r\<leftarrow>xml_nat (STR ''root'');
    k\<leftarrow>xml_nat (STR ''height'');
    m\<leftarrow>xml_nat (STR ''moduleRoot'');
    modules\<leftarrow>xml_many (STR ''modules'') lpc_return_module_data_parser id;
    actions\<leftarrow>xml_many (STR ''moduleActions'')
      (xml_many (STR ''moduleActions'') lpc_return_nested_action_parser id) id;
    Q\<leftarrow>xml_many (STR ''residual'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
    enc_pred\<leftarrow>xml_many (STR ''predicateEncoding'') (xml_pair (STR ''encoding'') lpc_symbol_parser symbol_parser Pair) id;
    enc_data\<leftarrow>xml_many (STR ''dataEncoding'') (xml_pair (STR ''encoding'') lpc_symbol_parser symbol_parser Pair) id;
    child\<leftarrow>lp_triple_pidp_parser;
    xml_return (P,q,modes,fuel,r,k,m,modules,actions,Q,enc_pred,enc_data,child)
  }"

definition check_lpc_return_nested_triples_xml where
  "check_lpc_return_nested_triples_xml xml = (case parse_xml_string lpc_return_nested_triples_parser xml of
    Right (P,q,modes,fuel,r,k,m,modules,actions,Q,enc_pred,enc_data,
      (D,R,outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs))\<Rightarrow>
      check_lpc_return_nested_triples tp_rbt_impl dpp_rbt_impl fuel k P Q modules actions m r q modes enc_pred enc_data
        D R outs fallback dnames pnames marks filters q' n positions labs proofs
    | _\<Rightarrow>False)"

theorem check_lpc_return_nested_triples_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpc_return_nested_triples_parser xml =
    Right (P,q,modes,fuel,r,k,m,modules,actions,Q,enc_pred,enc_data,
      (D,R,outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs))"
    and ok: "check_lpc_return_nested_triples_xml xml" and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_cut_mgu_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  by (rule check_lpc_return_nested_triples_sound[OF tp_rbt_impl dpp_rbt_impl _ len ground])
    (use parsed ok in \<open>simp add: check_lpc_return_nested_triples_xml_def\<close>)

end
