theory LP_Cut_SEG_Triple_XML
  imports LP_Cut_SEG_Triple_Certificate LP_Cut_SEG_Certificate_XML LP_Dependency_Triple_XML
begin

definition lpc_triple_root_parser where
  "lpc_triple_root_parser = XMLdo (STR ''tripleRoot'') {
    nd\<leftarrow>lpc_node_parser;
    inp\<leftarrow>xml_singleton (STR ''input'') lpc_atom_parser id;
    out\<leftarrow>xml_singleton (STR ''output'') lpc_atom_parser id;
    free\<leftarrow>xml_many (STR ''free'') (xml_text (STR ''var'')) id;
    xml_return \<lparr>lpctr_node=nd,lpctr_input=inp,
      lpctr_output=lpc_triple_position_atom (lpcn_vars nd) out,lpctr_free=free\<rparr>}"

definition lpc_triple_clause_receipt_parser where
  "lpc_triple_clause_receipt_parser = XMLdo (STR ''clauseReceipt'') {
    c\<leftarrow>xml_nat (STR ''index''); bs\<leftarrow>lpc_bindings_parser;
    xml_return (c,bs)}"

definition lpc_triple_position_receipt where
  "lpc_triple_position_receipt vs receipt =
    (fst receipt,map (\<lambda>(x,t). (x,lpc_seg_position_template vs t)) (snd receipt))"

definition lpc_triple_connection_parser where
  "lpc_triple_connection_parser = XMLdo (STR ''tripleConnection'') {
    vs\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
    target\<leftarrow>xml_nat (STR ''target''); bindings\<leftarrow>lpc_bindings_parser;
    swaps\<leftarrow>xml_many (STR ''swaps'') (xml_pair (STR ''swap'')
      (xml_nat (STR ''scope'')) (xml_nat (STR ''scope'')) Pair) id;
    dc\<leftarrow>xml_singleton (STR ''call'') lpc_triple_clause_receipt_parser id;
    pc\<leftarrow>xml_singleton (STR ''success'') lpc_triple_clause_receipt_parser id;
    xml_return \<lparr>lpctc_target=target,lpctc_bindings=bindings,lpctc_swaps=swaps,
      lpctc_call=fst dc,lpctc_call_bindings=snd dc,lpctc_success=fst pc,
      lpctc_success_bindings=snd (lpc_triple_position_receipt vs pc)\<rparr>}"

definition lpc_triple_region_parser where
  "lpc_triple_region_parser = XMLdo (STR ''tripleRegion'') {
    data\<leftarrow>lpc_seg_control_parser;
    Fs\<leftarrow>xml_many (STR ''freeKnowledge'')
      (xml_many (STR ''free'') (xml_text (STR ''var'')) id) id;
    connections\<leftarrow>xml_many (STR ''connections'') lpc_triple_connection_parser id;
    emits\<leftarrow>xml_many (STR ''emits'') lpc_triple_clause_receipt_parser id;
    xml_return \<lparr>lpctg_control=data,lpctg_free=Fs,lpctg_connections=connections,lpctg_emits=emits\<rparr>}"

definition lpc_triple_split_parser where
  "lpc_triple_split_parser = XMLdo (STR ''tripleSplit'') {
    vs\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
    pre\<leftarrow>xml_many (STR ''prefix'') lpc_goal_parser id;
    rest\<leftarrow>xml_many (STR ''rest'') lpc_goal_parser id;
    H\<leftarrow>xml_many (STR ''ground'') (xml_text (STR ''var'')) id;
    first\<leftarrow>xml_singleton (STR ''first'') lpc_seg_child_parser id;
    second\<leftarrow>xml_singleton (STR ''second'') lpc_seg_child_parser id;
    fi\<leftarrow>xml_singleton (STR ''firstInput'') lpc_atom_parser id;
    fo\<leftarrow>xml_singleton (STR ''firstOutput'') lpc_atom_parser id;
    si\<leftarrow>xml_singleton (STR ''secondInput'') lpc_atom_parser id;
    so\<leftarrow>xml_singleton (STR ''secondOutput'') lpc_atom_parser id;
    dc\<leftarrow>xml_singleton (STR ''firstCall'') lpc_triple_clause_receipt_parser id;
    ec\<leftarrow>xml_singleton (STR ''secondCall'') lpc_triple_clause_receipt_parser id;
    pc\<leftarrow>xml_singleton (STR ''success'') lpc_triple_clause_receipt_parser id;
    evidence\<leftarrow>lpc_seg_ground_evidence_parser;
    xml_return \<lparr>lpcts_pre = pre,lpcts_rest=rest,lpcts_ground=H,lpcts_first=first,lpcts_second=second,
      lpcts_first_in=fi,lpcts_first_out=lpc_triple_position_atom vs fo,
      lpcts_second_in=si,lpcts_second_out=lpc_triple_position_atom vs so,
      lpcts_first_call=dc,lpcts_second_call=lpc_triple_position_receipt vs ec,
      lpcts_success=lpc_triple_position_receipt vs pc,lpcts_ground_evidence=evidence\<rparr>}"

definition lpc_triple_component_parser where
  "lpc_triple_component_parser =
    (xml_change lpc_triple_region_parser (\<lambda>x. xml_return (LPCTRegion x))) XMLor
    (xml_change lpc_triple_split_parser (\<lambda>x. xml_return (LPCTSplit x)))"

definition lpc_seg_triples_parser where
  "lpc_seg_triples_parser = XMLdo (STR ''lpCutSEGDependencyTriplesProof'') {
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,bs)}) id;
    q\<leftarrow>xml_text (STR ''predicate'');
    modes\<leftarrow>xml_many (STR ''modes'') (xml_bool (STR ''mode'')) id;
    fuel\<leftarrow>xml_nat (STR ''fuel'');
    chain_pred\<leftarrow>xml_singleton (STR ''chainPredicate'') lpc_symbol_parser id;
    D\<leftarrow>xml_many (STR ''triples'') (XMLdo (STR ''triple'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      ps\<leftarrow>xml_many (STR ''prefix'') lpc_atom_parser id;
      b\<leftarrow>xml_singleton (STR ''call'') lpc_atom_parser id; xml_return (h,ps,b)}) id;
    Q\<leftarrow>xml_many (STR ''successProgram'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
    roots\<leftarrow>xml_many (STR ''roots'') lpc_triple_root_parser id;
    blocks\<leftarrow>xml_many (STR ''components'') lpc_triple_component_parser id;
    enc_pred\<leftarrow>lpc_seg_encoding_parser (STR ''predicateEncoding'');
    enc_data\<leftarrow>lpc_seg_encoding_parser (STR ''dataEncoding'');
    child\<leftarrow>lp_triple_pidp_parser;
    xml_return (P,q,modes,fuel,chain_pred,D,Q,roots,blocks,enc_pred,enc_data,child)}"

definition check_lpc_seg_triples_xml where
  "check_lpc_seg_triples_xml xml = (case parse_xml_string lpc_seg_triples_parser xml of
    Right (P,q,modes,fuel,chain_pred,D,Q,roots,blocks,enc_pred,enc_data,
      (D',Q',outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs)) \<Rightarrow>
      check_lpc_seg_triples tp_rbt_impl dpp_rbt_impl fuel P D Q roots blocks q modes chain_pred enc_pred enc_data
        D' Q' outs fallback dnames pnames marks filters q' n positions labs proofs
    | _ \<Rightarrow> False)"

theorem check_lpc_seg_triples_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpc_seg_triples_parser xml =
    Right (P,q,modes,fuel,chain_pred,D,Q,roots,blocks,enc_pred,enc_data,
      (D',Q',outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs))"
    and ok: "check_lpc_seg_triples_xml xml" and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_cut_mgu_source P)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  by (rule check_lpc_seg_triples_sound[OF tp_rbt_impl dpp_rbt_impl _ len ground])
    (use parsed ok in \<open>simp add: check_lpc_seg_triples_xml_def\<close>)

text \<open>Non-accepting diagnostics: parse, graph, exact child encoding,
child proof, then one Boolean for each source component.\<close>
definition lpc_seg_triples_diagnostics_xml where
  "lpc_seg_triples_diagnostics_xml xml = (case parse_xml_string lpc_seg_triples_parser xml of
    Right (P,q,modes,fuel,chain_pred,D,Q,roots,blocks,enc_pred,enc_data,
      (D',Q',outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs)) \<Rightarrow>
      [True,lpc_triple_check_graph fuel P D Q roots blocks q modes chain_pred,
       D'=lp_roles_triples (lpc_lookup fallback enc_pred) (lpc_lookup fallback enc_data) D \<and>
       Q'=lp_roles_program (lpc_lookup fallback enc_pred) (lpc_lookup fallback enc_data) Q \<and>
       q'=lpc_lookup fallback enc_pred chain_pred \<and> n=length modes \<and> positions=lpc_positions modes,
       check_lp_triple_pidp tp_rbt_impl dpp_rbt_impl D' Q' outs fallback dnames pnames marks filters q' n positions labs proofs]
      @ map (\<lambda>i. lpc_triple_check_component fuel P D Q roots (roots!i) (blocks!i)) [0..<length roots]
    | _ \<Rightarrow> [False])"

end
