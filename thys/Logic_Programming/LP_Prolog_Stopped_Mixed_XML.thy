theory LP_Prolog_Stopped_Mixed_XML
 imports LP_Prolog_Stopped_Mixed_Graph LP_Prolog_Stable_Mixed_XML
begin

definition lpp_stopped_control_parser where
  "lpp_stopped_control_parser = XMLdo (STR ''prologEvaluationControl'') {
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
       (XMLdo (STR ''undefinedProcedure'') {xml_return (Some LPPSUndefined)}) XMLor
       (xml_change lpp_evaluation_action_parser (\<lambda>a. xml_return (Some (LPPSControl a))))) id;
    Q\<leftarrow>xml_many (STR ''residual'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
    ranks\<leftarrow>xml_many (STR ''ranks'') (XMLdo (STR ''rank'') {
      f\<leftarrow>xml_singleton (STR ''symbol'') lpc_symbol_parser id;
      n\<leftarrow>xml_nat (STR ''value''); xml_return (f,n)}) id;
    xml_return (P,fuel,r,transfer,actions,
      \<lparr>lppftr_contexts=contexts,lppftr_typings=typings,lppftr_actions=map lpp_stopped_emit_action actions,lppftr_control=\<lparr>lpcsc_program=Q,lpcsc_nodes=nds,lpcsc_states=states,
        lpcsc_returned=returned,lpcsc_arity=arity,lpcsc_actions=[],lpcsc_ranks=ranks,lpcsc_boundaries=[]\<rparr>,
        lppftr_free=[],lppftr_connections=[],lppftr_emits=[]\<rparr>)}"


definition lpp_stopped_region_parser where
  "lpp_stopped_region_parser = XMLdo (STR ''prologTripleRegion'') {
    data\<leftarrow>lpp_stopped_control_parser;
    Fs\<leftarrow>xml_many (STR ''freeKnowledge'')
      (xml_many (STR ''free'') (xml_text (STR ''var'')) id) id;
    connections\<leftarrow>xml_many (STR ''connections'') lpc_triple_connection_parser id;
    emits\<leftarrow>xml_many (STR ''emits'') lpc_triple_clause_receipt_parser id;
    xml_return (case data of (P,fuel,r,transfer,actions,region) \<Rightarrow>
      (Some (P,fuel,r,transfer), actions,
        \<lparr>lppftr_contexts=lppftr_contexts region,
          lppftr_typings=lppftr_typings region,lppftr_actions=lppftr_actions region,
          lppftr_control=lppftr_control region,
          lppftr_free=Fs,lppftr_connections=connections,lppftr_emits=emits\<rparr>))}"

definition lpp_stopped_component_parser where
  "lpp_stopped_component_parser =
    (XMLdo (STR ''existingComponent'') {
      block\<leftarrow>lpp_stopped_region_parser;
      connections\<leftarrow>XMLdo (STR ''guardedRegion'') {
        cs\<leftarrow>xml_many (STR ''connections'') lpc_triple_connection_parser id; xml_return cs};
      xml_return (case block of (header,actions,region) \<Rightarrow>
        (header,LPPSStoppedRegion region actions connections))}) XMLor
    (XMLdo (STR ''relationalGroundSplit'') {
      split\<leftarrow>lpc_triple_split_parser;
      evidence\<leftarrow>lpp_finite_ground_receipt_parser;
      first_types\<leftarrow>lpp_evaluation_types_parser (STR ''firstTypes'');
      second_types\<leftarrow>lpp_evaluation_types_parser (STR ''secondTypes'');
      atom\<leftarrow>xml_singleton (STR ''returnedCall'') lpp_success_atom_parser id;
      first_call\<leftarrow>xml_singleton (STR ''firstCall'') lpc_triple_clause_receipt_parser id;
      second_call\<leftarrow>xml_singleton (STR ''secondCall'') lpc_triple_clause_receipt_parser id;
      xml_return (None,LPPSStoppedRelational first_types second_types split evidence atom first_call second_call)}) XMLor
    (XMLdo (STR ''relationalShapeSplit'') {
      split\<leftarrow>lpc_triple_split_parser;
      evidence\<leftarrow>lpp_finite_shape_receipt_parser;
      first_types\<leftarrow>lpp_evaluation_types_parser (STR ''firstTypes'');
      second_types\<leftarrow>lpp_evaluation_types_parser (STR ''secondTypes'');
      atom\<leftarrow>xml_singleton (STR ''returnedCall'') lpp_success_atom_parser id;
      first_call\<leftarrow>xml_singleton (STR ''firstCall'') lpc_triple_clause_receipt_parser id;
      second_call\<leftarrow>xml_singleton (STR ''secondCall'') lpc_triple_clause_receipt_parser id;
      xml_return (None,LPPSStoppedShape first_types second_types split evidence atom first_call second_call)})"

definition lpp_stopped_component_header where
  "lpp_stopped_component_header P fuel transfer component =
    (case component of (header,LPPSStoppedRegion region actions connections) \<Rightarrow>
      header=Some (P,fuel,0,transfer)
    | (header,LPPSStoppedRelational ft st split evidence atom first_call second_call) \<Rightarrow> header=None
    | (header,LPPSStoppedShape ft st split evidence atom first_call second_call) \<Rightarrow> header=None)"

definition lpp_established_stopped_mixed_parser where
  "lpp_established_stopped_mixed_parser = XMLdo (STR ''prologEstablishedStoppedSEGMixedProof'') {
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
    blocks\<leftarrow>xml_many (STR ''components'') lpp_stopped_component_parser id;
    OD\<leftarrow>xml_many (STR ''observedTriples'') lpp_observed_triple_parser id;
    ranks\<leftarrow>xml_many (STR ''routing'') (XMLdo (STR ''entry'') {
      p\<leftarrow>xml_text (STR ''predicate''); n\<leftarrow>xml_nat (STR ''rank''); xml_return (p,n)}) id;
    backends\<leftarrow>xml_many (STR ''backends'') lpp_mixed_backend_parser id;
    xml_return (profile,P,q,modes,fuel,chain_pred,D,Q,transfer,contexts,roots,blocks,OD,ranks,backends)}"

definition check_lpp_established_stopped_mixed_xml where
  "check_lpp_established_stopped_mixed_xml xml = (case parse_xml_string lpp_established_stopped_mixed_parser xml of
    Right (profile,P,q,modes,fuel,chain_pred,D,Q,(summaries,SP,receipts),contexts,roots,blocks,OD,ranks,raw) \<Rightarrow>
      (let candidates=lpp_decode_mixed_backends (summaries,SP,receipts) OD ranks raw in
        profile=''iso-rational-libraries-v1'' \<and>
        lpp_check_transfer_contract summaries SP receipts \<and>
        list_all (lpp_stopped_component_header P fuel (summaries,SP,receipts)) blocks \<and>
        distinct (map fst ranks) \<and>
        list_all (\<lambda>((h,ps,b,gs),os). fst h\<in>set (map fst ranks) \<and> fst b\<in>set (map fst ranks)) OD \<and>
        list_all (\<lambda>candidate. case candidate of None \<Rightarrow> False | Some _ \<Rightarrow> True) candidates \<and>
        lpp_check_stopped_mixed_graph tp_rbt_impl dpp_rbt_impl fuel P D Q (lpp_transfer_lookup summaries) SP receipts
          roots contexts (map snd blocks) q modes chain_pred OD (lpp_mixed_rank_lookup ranks) (map the candidates))
    | _ \<Rightarrow> False)"

theorem check_lpp_established_stopped_mixed_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpp_established_stopped_mixed_parser xml =
    Right (profile,P,q,modes,fuel,chain_pred,D,Q,(summaries,SP,receipts),contexts,roots,blocks,OD,ranks,raw)"
    and ok: "check_lpp_established_stopped_mixed_xml xml"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lp_prolog_source P lpp_builtin_signature (lpp_domain_source P lpp_builtin_signature (lpp_stable_source_builtin (lpp_stable_profile_operation fallback)) lpp_finite_source_domain))
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof -
  have checked: "lpp_check_stopped_mixed_graph tp_rbt_impl dpp_rbt_impl fuel P D Q (lpp_transfer_lookup summaries) SP receipts
      roots contexts (map snd blocks) q modes chain_pred OD (lpp_mixed_rank_lookup ranks)
      (map the (lpp_decode_mixed_backends (summaries,SP,receipts) OD ranks raw))"
    using parsed ok by (auto simp: check_lpp_established_stopped_mixed_xml_def Let_def)
  show ?thesis
  proof (rule lpp_check_stopped_mixed_graph_sound[OF tp_rbt_impl dpp_rbt_impl lpp_stable_profile_integer_compatible checked])
    show "length (map (\<lambda>t. lp_ieval t LPIVar) ts)=length modes" using len by simp
    show "\<forall>(t,b)\<in>set (zip (map (\<lambda>t. lp_ieval t LPIVar) ts) modes). b \<longrightarrow> lp_seg_ground t"
      using ground len by (auto simp: in_set_zip lpc_positions_def lp_seg_ground_eval ground_vars_term_empty)
  qed
qed

ML \<open>
val checked = [@{thm check_lpp_established_stopped_mixed_xml_sound}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles checked))
  then error "Untrusted mixed source XML" else ();
\<close>
end
