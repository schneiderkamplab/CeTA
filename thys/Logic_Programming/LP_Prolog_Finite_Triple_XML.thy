theory LP_Prolog_Finite_Triple_XML
 imports LP_Prolog_Finite_Triple_Certificate LP_Prolog_Evaluation_XML LP_Cut_SEG_Triple_XML
begin

definition lpp_established_finite_control_parser where
  "lpp_established_finite_control_parser = XMLdo (STR ''prologEvaluationControl'') {
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
       (xml_change lpp_evaluation_action_parser (\<lambda>a. xml_return (Some a)))) id;
    Q\<leftarrow>xml_many (STR ''residual'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
    ranks\<leftarrow>xml_many (STR ''ranks'') (XMLdo (STR ''rank'') {
      f\<leftarrow>xml_singleton (STR ''symbol'') lpc_symbol_parser id;
      n\<leftarrow>xml_nat (STR ''value''); xml_return (f,n)}) id;
    xml_return (P,fuel,r,transfer,
      \<lparr>lppftr_contexts=contexts,lppftr_typings=typings,lppftr_actions=actions,lppftr_control=\<lparr>lpcsc_program=Q,lpcsc_nodes=nds,lpcsc_states=states,
        lpcsc_returned=returned,lpcsc_arity=arity,lpcsc_actions=[],lpcsc_ranks=ranks,lpcsc_boundaries=[]\<rparr>,
        lppftr_free=[],lppftr_connections=[],lppftr_emits=[]\<rparr>)}"


definition lpp_established_finite_region_parser where
  "lpp_established_finite_region_parser = XMLdo (STR ''prologTripleRegion'') {
    data\<leftarrow>lpp_established_finite_control_parser;
    Fs\<leftarrow>xml_many (STR ''freeKnowledge'')
      (xml_many (STR ''free'') (xml_text (STR ''var'')) id) id;
    connections\<leftarrow>xml_many (STR ''connections'') lpc_triple_connection_parser id;
    emits\<leftarrow>xml_many (STR ''emits'') lpc_triple_clause_receipt_parser id;
    xml_return (case data of (P,fuel,r,transfer,region) \<Rightarrow>
      (Some (P,fuel,r,transfer), LPPFTRegion
        \<lparr>lppftr_contexts=lppftr_contexts region,
          lppftr_typings=lppftr_typings region,lppftr_actions=lppftr_actions region,
          lppftr_control=lppftr_control region,
          lppftr_free=Fs,lppftr_connections=connections,lppftr_emits=emits\<rparr>))}"

definition lpp_established_finite_split_parser where
  "lpp_established_finite_split_parser = XMLdo (STR ''prologTripleSplit'') {
    split\<leftarrow>lpc_triple_split_parser;
    first_types\<leftarrow>lpp_evaluation_types_parser (STR ''firstTypes'');
    second_types\<leftarrow>lpp_evaluation_types_parser (STR ''secondTypes'');
    xml_return (None,LPPFTSplit first_types second_types split)}"

definition lpp_finite_integer_receipt_parser where
  "lpp_finite_integer_receipt_parser = XMLdo (STR ''sourceIntegerReturn'') {
    model\<leftarrow>XMLdo (STR ''sourceFiniteReturnModel'') {
      F\<leftarrow>xml_many (STR ''predicates'') (xml_text (STR ''predicate'')) id;
      transfer\<leftarrow>lpp_transfer_contract_parser;
      xml_return (F,transfer)};
    facts\<leftarrow>xml_many (STR ''facts'') lpp_transfer_fact_parser id;
    K\<leftarrow>xml_many (STR ''integers'') (xml_text (STR ''var'')) id;
    xml_return (case model of (F,(summaries,SP,proofs)) \<Rightarrow>
      \<lparr>lppsir_predicates = F,lppsir_summaries = summaries,lppsir_program = SP,
        lppsir_proofs = proofs,lppsir_facts = facts,lppsir_integers = K\<rparr>)}"

definition lpp_established_finite_integer_split_parser where
  "lpp_established_finite_integer_split_parser = XMLdo (STR ''prologTripleIntegerSplit'') {
    split\<leftarrow>lpc_triple_split_parser;
    evidence\<leftarrow>lpp_finite_integer_receipt_parser;
    first_types\<leftarrow>lpp_evaluation_types_parser (STR ''firstTypes'');
    second_types\<leftarrow>lpp_evaluation_types_parser (STR ''secondTypes'');
    xml_return (None,LPPFTIntegerSplit first_types second_types split evidence)}"

definition lpp_finite_ground_receipt_parser where
  "lpp_finite_ground_receipt_parser = XMLdo (STR ''sourceGroundReturn'') {
    model\<leftarrow>XMLdo (STR ''sourceFiniteReturnModel'') {
      F\<leftarrow>xml_many (STR ''predicates'') (xml_text (STR ''predicate'')) id;
      transfer\<leftarrow>lpp_transfer_contract_parser; xml_return (F,transfer)};
    modes\<leftarrow>xml_many (STR ''groundModes'') (XMLdo (STR ''groundMode'') {
      f\<leftarrow>xml_singleton (STR ''symbol'') lpc_symbol_parser id;
      n\<leftarrow>xml_nat (STR ''arity'');
      pins\<leftarrow>xml_many (STR ''inputs'') (xml_nat (STR ''position'')) id;
      pouts\<leftarrow>xml_many (STR ''outputs'') (xml_nat (STR ''position'')) id;
      xml_return (LPGroundMode f n pins pouts)}) id;
    K\<leftarrow>xml_many (STR ''ground'') (xml_text (STR ''var'')) id;
    xml_return (case model of (F,(summaries,SP,proofs)) \<Rightarrow>
      \<lparr>lppsgr_model = \<lparr>lppsir_predicates = F,lppsir_summaries = summaries,lppsir_program = SP,
        lppsir_proofs = proofs,lppsir_facts = [],lppsir_integers = []\<rparr>,
        lppsgr_modes = modes,lppsgr_ground = K\<rparr>)}"

definition lpp_established_finite_ground_split_parser where
  "lpp_established_finite_ground_split_parser = XMLdo (STR ''prologTripleGroundSplit'') {
    split\<leftarrow>lpc_triple_split_parser;
    evidence\<leftarrow>lpp_finite_ground_receipt_parser;
    first_types\<leftarrow>lpp_evaluation_types_parser (STR ''firstTypes'');
    second_types\<leftarrow>lpp_evaluation_types_parser (STR ''secondTypes'');
    xml_return (None,LPPFTGroundSplit first_types second_types split evidence)}"

definition lpp_shape_fact_parser where
  "lpp_shape_fact_parser = XMLdo (STR ''shapeFact'') {
    shape\<leftarrow>xml_singleton (STR ''shape'') lpp_return_shape_parser id;
    x\<leftarrow>xml_text (STR ''var''); xml_return (shape,x)}"

definition lpp_finite_shape_receipt_parser where
  "lpp_finite_shape_receipt_parser = XMLdo (STR ''sourceShapeReturn'') {
    base\<leftarrow>lpp_finite_ground_receipt_parser;
    facts\<leftarrow>xml_many (STR ''integerFacts'') lpp_transfer_fact_parser id;
    integers\<leftarrow>xml_many (STR ''integers'') (xml_text (STR ''var'')) id;
    fuel\<leftarrow>xml_nat (STR ''shapeFuel'');
    grammar\<leftarrow>lpp_return_grammar_parser;
    modes\<leftarrow>xml_many (STR ''shapeContracts'') (XMLdo (STR ''shapeContract'') {
      f\<leftarrow>xml_singleton (STR ''symbol'') lpc_symbol_parser id;
      inputs\<leftarrow>xml_many (STR ''inputs'') lpp_return_shape_parser id;
      outputs\<leftarrow>xml_many (STR ''outputs'') lpp_return_shape_parser id;
      xml_return (f,inputs,outputs)}) id;
    seeds\<leftarrow>xml_many (STR ''seeds'') lpp_shape_fact_parser id;
    outputs\<leftarrow>xml_many (STR ''outputs'') lpp_shape_fact_parser id;
    xml_return \<lparr>lppssr_ground = base\<lparr>lppsgr_model :=
        (lppsgr_model base)\<lparr>lppsir_facts := facts,lppsir_integers := integers\<rparr>\<rparr>,
      lppssr_fuel = fuel,lppssr_grammar = grammar,lppssr_modes = modes,lppssr_seeds = seeds,lppssr_outputs = outputs\<rparr>}"

definition lpp_established_finite_shape_split_parser where
  "lpp_established_finite_shape_split_parser = XMLdo (STR ''prologTripleShapeSplit'') {
    split\<leftarrow>lpc_triple_split_parser;
    evidence\<leftarrow>lpp_finite_shape_receipt_parser;
    first_types\<leftarrow>lpp_evaluation_types_parser (STR ''firstTypes'');
    second_types\<leftarrow>lpp_evaluation_types_parser (STR ''secondTypes'');
    xml_return (None,LPPFTShapeSplit first_types second_types split evidence)}"

definition lpp_established_finite_component_parser where
  "lpp_established_finite_component_parser = lpp_established_finite_region_parser XMLor lpp_established_finite_split_parser XMLor lpp_established_finite_integer_split_parser XMLor lpp_established_finite_ground_split_parser XMLor lpp_established_finite_shape_split_parser"

fun lpp_established_finite_component_header where
  "lpp_established_finite_component_header P fuel transfer (None,component) = True"
| "lpp_established_finite_component_header P fuel transfer (Some (P',fuel',r,transfer'),component) =
    (P=P' \<and> fuel=fuel' \<and> r=0 \<and> transfer=transfer')"

definition lpp_established_finite_triples_parser where
  "lpp_established_finite_triples_parser = XMLdo (STR ''prologEstablishedFiniteSEGDependencyTriplesProof'') {
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
    blocks\<leftarrow>xml_many (STR ''components'') lpp_established_finite_component_parser id;
    enc_pred\<leftarrow>lpc_seg_encoding_parser (STR ''predicateEncoding'');
    enc_data\<leftarrow>lpc_seg_encoding_parser (STR ''dataEncoding'');
    child\<leftarrow>lp_triple_pidp_parser;
    xml_return (profile,P,q,modes,fuel,chain_pred,D,Q,transfer,contexts,roots,blocks,enc_pred,enc_data,child)}"

definition check_lpp_established_finite_triples_xml where
  "check_lpp_established_finite_triples_xml xml = (case parse_xml_string lpp_established_finite_triples_parser xml of
    Right (profile,P,q,modes,fuel,chain_pred,D,Q,(summaries,SP,receipts),contexts,roots,blocks,enc_pred,enc_data,
      (D',Q',outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs)) \<Rightarrow>
      profile=''iso-rational-libraries-v1'' \<and>
      lpp_check_transfer_contract summaries SP receipts \<and>
      list_all (lpp_established_finite_component_header P fuel (summaries,SP,receipts)) blocks \<and>
      check_lpp_established_finite_triples tp_rbt_impl dpp_rbt_impl fuel P D Q (lpp_transfer_lookup summaries) roots contexts (map snd blocks) q modes chain_pred enc_pred enc_data
        D' Q' outs fallback dnames pnames marks filters q' n positions labs proofs
    | _ \<Rightarrow> False)"

theorem check_lpp_established_finite_triples_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpp_established_finite_triples_parser xml =
    Right (profile,P,q,modes,fuel,chain_pred,D,Q,(summaries,SP,receipts),contexts,roots,blocks,enc_pred,enc_data,
      (D',Q',outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs))"
    and ok: "check_lpp_established_finite_triples_xml xml" and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature lpp_finite_source_builtin lpp_finite_source_domain)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  by (rule check_lpp_established_finite_triples_sound[OF tp_rbt_impl dpp_rbt_impl _ _ len ground])
    (use parsed ok in \<open>auto simp: check_lpp_established_finite_triples_xml_def lpp_check_transfer_contract_def\<close>)

text \<open>Non-accepting diagnostics: parse, graph, exact child encoding,
child proof, then one Boolean for each source component.\<close>
definition lpp_established_finite_triples_diagnostics_xml where
  "lpp_established_finite_triples_diagnostics_xml xml = (case parse_xml_string lpp_established_finite_triples_parser xml of
    Right (profile,P,q,modes,fuel,chain_pred,D,Q,(summaries,SP,receipts),contexts,roots,blocks,enc_pred,enc_data,
      (D',Q',outs,fallback,dnames,pnames,marks,filters,(q',n,positions),labs,proofs)) \<Rightarrow>
      [True,lpp_finite_triple_check_graph fuel P D Q (lpp_transfer_lookup summaries) roots contexts (map snd blocks) q modes chain_pred,
       D'=lp_roles_triples (lpc_lookup fallback enc_pred) (lpc_lookup fallback enc_data) D \<and>
       Q'=lp_roles_program (lpc_lookup fallback enc_pred) (lpc_lookup fallback enc_data) Q \<and>
       q'=lpc_lookup fallback enc_pred chain_pred \<and> n=length modes \<and> positions=lpc_positions modes,
       check_lp_triple_pidp tp_rbt_impl dpp_rbt_impl D' Q' outs fallback dnames pnames marks filters q' n positions labs proofs]
      @ map (\<lambda>i. lpp_finite_triple_check_component fuel P D Q (lpp_transfer_lookup summaries) roots contexts (contexts!i) (roots!i) (snd (blocks!i))) [0..<length roots]
    | _ \<Rightarrow> [False])"

ML \<open>
val checked = [@{thm check_lpp_established_finite_triples_xml_sound},
  @{thm lpp_finite_triple_graph_root_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted established source graph dependency" else ();
\<close>

end
