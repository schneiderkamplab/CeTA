theory LP_Prolog_Triple_XML
 imports LP_Prolog_Triple_Certificate LP_Prolog_Context_Region LP_Prolog_Context_Module_XML LP_Cut_SEG_Triple_XML
begin

definition lpp_established_control_parser where
  "lpp_established_control_parser = XMLdo (STR ''prologContextControl'') {
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
    actions\<leftarrow>xml_many (STR ''actions'')
      ((XMLdo (STR ''boundary'') {xml_return None}) XMLor
       (xml_change lpp_context_module_action_parser (\<lambda>a. xml_return (Some a)))) id;
    Q\<leftarrow>xml_many (STR ''residual'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
    ranks\<leftarrow>xml_many (STR ''ranks'') (XMLdo (STR ''rank'') {
      f\<leftarrow>xml_singleton (STR ''symbol'') lpc_symbol_parser id;
      n\<leftarrow>xml_nat (STR ''value''); xml_return (f,n)}) id;
    xml_return (P,fuel,r,transfer,
      \<lparr>lppcr_control=\<lparr>lpcsc_program=Q,lpcsc_nodes=nds,lpcsc_states=states,
        lpcsc_returned=returned,lpcsc_arity=arity,lpcsc_actions=[],lpcsc_ranks=ranks,lpcsc_boundaries=[]\<rparr>,
        lppcr_contexts=contexts,lppcr_typings=typings,lppcr_actions=actions,lppcr_connections=[]\<rparr>)}"


definition lpp_established_region_parser where
  "lpp_established_region_parser = XMLdo (STR ''prologTripleRegion'') {
    data\<leftarrow>lpp_established_control_parser;
    Fs\<leftarrow>xml_many (STR ''freeKnowledge'')
      (xml_many (STR ''free'') (xml_text (STR ''var'')) id) id;
    connections\<leftarrow>xml_many (STR ''connections'') lpc_triple_connection_parser id;
    emits\<leftarrow>xml_many (STR ''emits'') lpc_triple_clause_receipt_parser id;
    xml_return (case data of (P,fuel,r,transfer,region) \<Rightarrow>
      (Some (P,fuel,r,transfer), LPPTRegion
        \<lparr>lpptr_contexts=lppcr_contexts region,
          lpptr_typings=lppcr_typings region,lpptr_actions=lppcr_actions region,
          lpptr_control=lppcr_control region,
          lpptr_free=Fs,lpptr_connections=connections,lpptr_emits=emits\<rparr>))}"

definition lpp_established_split_parser where
  "lpp_established_split_parser = XMLdo (STR ''prologTripleSplit'') {
    A\<leftarrow>xml_many (STR ''staticPredicates'') (XMLdo (STR ''signature'') {
      f\<leftarrow>xml_text (STR ''name''); n\<leftarrow>xml_nat (STR ''arity''); xml_return (f,n)}) id;
    split\<leftarrow>lpc_triple_split_parser;
    xml_return (None,LPPTSplit A split)}"

definition lpp_source_integer_receipt_parser where
  "lpp_source_integer_receipt_parser = XMLdo (STR ''sourceIntegerReturn'') {
    model\<leftarrow>XMLdo (STR ''sourceReturnModel'') {
      F\<leftarrow>xml_many (STR ''predicates'') (xml_text (STR ''predicate'')) id;
      transfer\<leftarrow>lpp_transfer_contract_parser;
      xml_return (F,transfer)};
    facts\<leftarrow>xml_many (STR ''facts'') lpp_transfer_fact_parser id;
    K\<leftarrow>xml_many (STR ''integers'') (xml_text (STR ''var'')) id;
    xml_return (case model of (F,(summaries,SP,proofs)) \<Rightarrow>
      \<lparr>lppsir_predicates = F,lppsir_summaries = summaries,lppsir_program = SP,
        lppsir_proofs = proofs,lppsir_facts = facts,lppsir_integers = K\<rparr>)}"

definition lpp_established_integer_split_parser where
  "lpp_established_integer_split_parser = XMLdo (STR ''prologTripleIntegerSplit'') {
    split\<leftarrow>lpc_triple_split_parser;
    evidence\<leftarrow>lpp_source_integer_receipt_parser;
    xml_return (None,LPPTIntegerSplit split evidence)}"

definition lpp_established_component_parser where
  "lpp_established_component_parser = lpp_established_region_parser XMLor lpp_established_split_parser XMLor lpp_established_integer_split_parser"

fun lpp_established_component_header where
  "lpp_established_component_header P fuel transfer (None,component) = True"
| "lpp_established_component_header P fuel transfer (Some (P',fuel',r,transfer'),component) =
    (P=P' \<and> fuel=fuel' \<and> r=0 \<and> transfer=transfer')"

definition lpp_established_triples_parser where
  "lpp_established_triples_parser = XMLdo (STR ''prologEstablishedSEGDependencyTriplesProof'') {
    profile\<leftarrow>xml_text (STR ''profile'');
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
    transfer\<leftarrow>lpp_transfer_contract_parser;
    contexts\<leftarrow>xml_many (STR ''contexts'') lpp_source_context_parser id;
    roots\<leftarrow>xml_many (STR ''roots'') lpc_triple_root_parser id;
    blocks\<leftarrow>xml_many (STR ''components'') lpp_established_component_parser id;
    enc_pred\<leftarrow>lpc_seg_encoding_parser (STR ''predicateEncoding'');
    enc_data\<leftarrow>lpc_seg_encoding_parser (STR ''dataEncoding'');
    child\<leftarrow>lp_triple_pidp_parser;
    xml_return (profile,P,q,modes,fuel,chain_pred,D,Q,transfer,contexts,roots,blocks,enc_pred,enc_data,child)}"

definition check_lpp_established_triples_xml where
  "check_lpp_established_triples_xml xml = (case parse_xml_string lpp_established_triples_parser xml of
    Right (profile,P,q,modes,fuel,chain_pred,D,Q,(summaries,SP,receipts),contexts,roots,blocks,enc_pred,enc_data,
      (D',Q',outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs)) \<Rightarrow>
      profile=''iso-rational-libraries-v1'' \<and>
      lpp_check_transfer_contract summaries SP receipts \<and>
      list_all (lpp_established_component_header P fuel (summaries,SP,receipts)) blocks \<and>
      check_lpp_established_triples tp_rbt_impl dpp_rbt_impl fuel P D Q (lpp_transfer_lookup summaries) roots contexts (map snd blocks) q modes chain_pred enc_pred enc_data
        D' Q' outs fallback dnames pnames marks filters q' n positions labs proofs
    | _ \<Rightarrow> False)"

theorem check_lpp_established_triples_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpp_established_triples_parser xml =
    Right (profile,P,q,modes,fuel,chain_pred,D,Q,(summaries,SP,receipts),contexts,roots,blocks,enc_pred,enc_data,
      (D',Q',outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs))"
    and ok: "check_lpp_established_triples_xml xml" and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  by (rule check_lpp_established_triples_sound[OF tp_rbt_impl dpp_rbt_impl _ _ len ground])
    (use parsed ok in \<open>auto simp: check_lpp_established_triples_xml_def lpp_check_transfer_contract_def\<close>)

text \<open>Non-accepting diagnostics: parse, graph, exact child encoding,
child proof, then one Boolean for each source component.\<close>
definition lpp_established_triples_diagnostics_xml where
  "lpp_established_triples_diagnostics_xml xml = (case parse_xml_string lpp_established_triples_parser xml of
    Right (profile,P,q,modes,fuel,chain_pred,D,Q,(summaries,SP,receipts),contexts,roots,blocks,enc_pred,enc_data,
      (D',Q',outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs)) \<Rightarrow>
      [True,lpp_triple_check_graph fuel P D Q (lpp_transfer_lookup summaries) roots contexts (map snd blocks) q modes chain_pred,
       D'=lp_roles_triples (lpc_lookup fallback enc_pred) (lpc_lookup fallback enc_data) D \<and>
       Q'=lp_roles_program (lpc_lookup fallback enc_pred) (lpc_lookup fallback enc_data) Q \<and>
       q'=lpc_lookup fallback enc_pred chain_pred \<and> n=length modes \<and> positions=lpc_positions modes,
       check_lp_triple_pidp tp_rbt_impl dpp_rbt_impl D' Q' outs fallback dnames pnames marks filters q' n positions labs proofs]
      @ map (\<lambda>i. lpp_triple_check_component fuel P D Q (lpp_transfer_lookup summaries) roots contexts (contexts!i) (roots!i) (snd (blocks!i))) [0..<length roots]
    | _ \<Rightarrow> [False])"

ML \<open>
val checked = [@{thm check_lpp_established_triples_xml_sound},
  @{thm lpp_triple_graph_root_sound}, @{thm lpp_triple_split_checked_lower},
  @{thm lpp_context_free_resolution_node_sound}, @{thm lpp_observed_actual_context},
  @{thm lpp_cyclic_spine_not_finite}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted established source graph dependency" else ();
\<close>

end
