theory LP_Cut_Projected_XML
  imports LP_Cut_Projected_Certificate LP_Cut_Return_Nested_XML
begin

derive (eq) ceq lp_cut_symbol
derive ccompare lp_cut_symbol
derive (rbt) set_impl lp_cut_symbol

definition lpc_projected_clauses_parser where
  "lpc_projected_clauses_parser = xml_many (STR ''residual'') (XMLdo (STR ''clause'') {
    h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
    bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id"

definition lpc_projected_action_parser where
  "lpc_projected_action_parser =
    (XMLdo (STR ''projectedPlain'') {
      Q\<leftarrow>lpc_projected_clauses_parser;
      a\<leftarrow>lpc_return_module_action_parser;
      xml_return (LPCPPlain Q a)}) XMLor
    (XMLdo (STR ''projectedRefreshed'') {
      Q\<leftarrow>lpc_projected_clauses_parser;
      a\<leftarrow>lpc_return_action_parser;
      vs\<leftarrow>xml_many (STR ''refreshVariables'') (xml_text (STR ''var'')) id;
      l\<leftarrow>xml_singleton (STR ''left'') lpc_term_parser id;
      r\<leftarrow>xml_singleton (STR ''right'') lpc_term_parser id;
      xml_return (LPCPRefreshed Q a vs l r)})"

definition lpc_projected_nested_action_parser where
  "lpc_projected_nested_action_parser =
    (xml_change lpc_projected_action_parser (\<lambda>a. xml_return (LPCPTLocal a))) XMLor
    (XMLdo (STR ''nestedReturnSplit'') {
      bindings\<leftarrow>xml_many (STR ''routing'') (xml_pair (STR ''route'') (xml_text (STR ''var'')) (xml_nat (STR ''index'')) Pair) id;
      indices\<leftarrow>xml_many (STR ''projection'') (xml_nat (STR ''index'')) id;
      pre\<leftarrow>xml_many (STR ''prefix'') lpc_goal_parser id;
      rest\<leftarrow>xml_many (STR ''continuation'') lpc_goal_parser id;
      interface\<leftarrow>xml_many (STR ''interface'') lpc_term_parser id;
      prefix_module\<leftarrow>xml_nat (STR ''prefixModule'');
      prefix_link\<leftarrow>lpc_link_parser;
      vs\<leftarrow>xml_many (STR ''returnVariables'') (xml_text (STR ''var'')) id;
      continuation_module\<leftarrow>xml_nat (STR ''continuationModule'');
      continuation_link\<leftarrow>lpc_link_parser;
      xml_return (LPCPTSplit bindings indices pre rest interface prefix_module prefix_link vs continuation_module continuation_link)}) XMLor
    (XMLdo (STR ''nestedGroundReturnSplit'') {
      bindings\<leftarrow>xml_many (STR ''routing'') (xml_pair (STR ''route'') (xml_text (STR ''var'')) (xml_nat (STR ''index'')) Pair) id;
      indices\<leftarrow>xml_many (STR ''projection'') (xml_nat (STR ''index'')) id;
      pre\<leftarrow>xml_many (STR ''prefix'') lpc_goal_parser id;
      rest\<leftarrow>xml_many (STR ''continuation'') lpc_goal_parser id;
      interface\<leftarrow>xml_many (STR ''interface'') lpc_term_parser id;
      prefix_module\<leftarrow>xml_nat (STR ''prefixModule'');
      prefix_link\<leftarrow>lpc_link_parser;
      vs\<leftarrow>xml_many (STR ''returnVariables'') (xml_text (STR ''var'')) id;
      continuation_module\<leftarrow>xml_nat (STR ''continuationModule'');
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
      xml_return (LPCPTGroundSplit bindings indices pre rest interface prefix_module prefix_link vs continuation_module continuation_link positions groundQ Fs modes)})"
definition lpc_projected_certificate_parser where
  "lpc_projected_certificate_parser = XMLdo (STR ''lpCutProjectedGraphTerminationProof'') {
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
      (xml_many (STR ''moduleActions'') lpc_projected_nested_action_parser id) id;
    Q\<leftarrow>xml_many (STR ''residual'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
    R\<leftarrow>xml_many (STR ''rules'')
      (xml_pair (STR ''rule'') (xml_singleton (STR ''lhs'') lpc_term_parser id)
        (xml_singleton (STR ''rhs'') lpc_term_parser id) Pair) id;
    enc\<leftarrow>xml_many (STR ''encoding'') (xml_pair (STR ''entry'') lpc_symbol_parser symbol_parser Pair) id;
    fallback\<leftarrow>xml_singleton (STR ''fallback'') symbol_parser id;
    filters\<leftarrow>CPF_Proof_Parser.afs lpc_symbol_parser;
    prf\<leftarrow>xml2trs_termination_proof symbol_parser Mapping.empty Mapping.empty;
    xml_return (P,q,modes,fuel,r,k,m,modules,actions,Q,R,enc,fallback,filters,prf)
  }"

definition check_lpc_projected_xml where
  "check_lpc_projected_xml xml = (case parse_xml_string lpc_projected_certificate_parser xml of
    Right (P,q,modes,fuel,r,k,m,modules,actions,Q,R,enc,fallback,filters,prf) \<Rightarrow>
      check_lpc_projected_certificate tp_rbt_impl dpp_rbt_impl (lpc_lookup fallback enc)
        fuel k P filters R Q modules actions m r q modes prf
    | _ \<Rightarrow> False)"

theorem check_lpc_projected_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpc_projected_certificate_parser xml =
    Right (P,q,modes,fuel,r,k,m,modules,actions,Q,R,enc,fallback,filters,prf)"
    and ok: "check_lpc_projected_xml xml" and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_cut_mgu_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  by (rule check_lpc_projected_certificate_sound[OF tp_rbt_impl dpp_rbt_impl _ len ground])
    (use parsed ok in \<open>simp add: check_lpc_projected_xml_def\<close>)

end
