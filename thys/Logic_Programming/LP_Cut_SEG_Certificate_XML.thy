theory LP_Cut_SEG_Certificate_XML
  imports LP_Cut_SEG_Certificate LP_Cut_SEG_Measure_XML
begin

definition lpc_seg_root_parser where
  "lpc_seg_root_parser = XMLdo (STR ''segRoot'') {
    nd\<leftarrow>lpc_node_parser;
    inp\<leftarrow>xml_singleton (STR ''input'') lpc_term_parser id;
    out\<leftarrow>xml_singleton (STR ''output'') lpc_term_parser id;
    xml_return \<lparr>lpcsr_node=nd,lpcsr_input=inp,
      lpcsr_output=lpc_seg_position_template (lpcn_vars nd) out\<rparr>}"

definition lpc_seg_connection_parser where
  "lpc_seg_connection_parser = XMLdo (STR ''connection'') {
    target\<leftarrow>xml_nat (STR ''target''); bindings\<leftarrow>lpc_bindings_parser;
    swaps\<leftarrow>xml_many (STR ''swaps'') (xml_pair (STR ''swap'')
      (xml_nat (STR ''scope'')) (xml_nat (STR ''scope'')) Pair) id;
    u\<leftarrow>xml_singleton (STR ''continuation'') lpc_symbol_parser id;
    caps\<leftarrow>xml_many (STR ''captured'') lpc_term_parser id;
    Q\<leftarrow>xml_many (STR ''groundProgram'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
    Fs\<leftarrow>xml_many (STR ''predicates'') (xml_text (STR ''predicate'')) id;
    modes\<leftarrow>xml_many (STR ''groundModes'') (XMLdo (STR ''groundMode'') {
      f\<leftarrow>xml_singleton (STR ''symbol'') lpc_symbol_parser id;
      n\<leftarrow>xml_nat (STR ''arity'');
      pins\<leftarrow>xml_many (STR ''inputs'') (xml_nat (STR ''position'')) id;
      pouts\<leftarrow>xml_many (STR ''outputs'') (xml_nat (STR ''position'')) id;
      xml_return (LPGroundMode f n pins pouts)}) id;
    xml_return \<lparr>lpcse_target=target,lpcse_bindings=bindings,lpcse_swaps=swaps,
      lpcse_continuation=u,lpcse_captured=caps,lpcse_ground_program=Q,
      lpcse_predicates=Fs,lpcse_modes=modes\<rparr>}"

definition lpc_seg_region_parser where
  "lpc_seg_region_parser = XMLdo (STR ''region'') {
    data\<leftarrow>lpc_seg_control_parser; templates\<leftarrow>lpc_seg_templates_parser;
    connections\<leftarrow>xml_many (STR ''connections'') (XMLdo (STR ''boundary'') {
      i\<leftarrow>xml_nat (STR ''local''); receipt\<leftarrow>lpc_seg_connection_parser;
      xml_return (i,receipt)}) id;
    xml_return \<lparr>lpcsg_control=data,lpcsg_templates=templates,lpcsg_connections=connections\<rparr>}"

definition lpc_seg_encoding_parser where
  "lpc_seg_encoding_parser tag = xml_many tag
    (xml_pair (STR ''encoding'') lpc_symbol_parser symbol_parser Pair) id"

definition lpc_seg_child_parser where
  "lpc_seg_child_parser = XMLdo (STR ''child'') {
    i\<leftarrow>xml_nat (STR ''target''); bs\<leftarrow>lpc_bindings_parser;
    swaps\<leftarrow>xml_many (STR ''swaps'') (xml_pair (STR ''swap'')
      (xml_nat (STR ''scope'')) (xml_nat (STR ''scope'')) Pair) id;
    xml_return \<lparr>lpcsh_target=i,lpcsh_bindings=bs,lpcsh_swaps=swaps\<rparr>}"

definition lpc_seg_ground_evidence_parser where
  "lpc_seg_ground_evidence_parser = XMLdo (STR ''groundEvidence'') {
    Q\<leftarrow>xml_many (STR ''groundProgram'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
    Fs\<leftarrow>xml_many (STR ''predicates'') (xml_text (STR ''predicate'')) id;
    modes\<leftarrow>xml_many (STR ''groundModes'') (XMLdo (STR ''groundMode'') {
      f\<leftarrow>xml_singleton (STR ''symbol'') lpc_symbol_parser id;
      n\<leftarrow>xml_nat (STR ''arity'');
      pins\<leftarrow>xml_many (STR ''inputs'') (xml_nat (STR ''position'')) id;
      pouts\<leftarrow>xml_many (STR ''outputs'') (xml_nat (STR ''position'')) id;
      xml_return (LPGroundMode f n pins pouts)}) id;
    xml_return \<lparr>lpcsk_program=Q,lpcsk_predicates=Fs,lpcsk_modes=modes\<rparr>}"

definition lpc_seg_split_parser where
  "lpc_seg_split_parser = XMLdo (STR ''segSplit'') {
    pre\<leftarrow>xml_many (STR ''prefix'') lpc_goal_parser id;
    rest\<leftarrow>xml_many (STR ''rest'') lpc_goal_parser id;
    H\<leftarrow>xml_many (STR ''ground'') (xml_text (STR ''var'')) id;
    first\<leftarrow>xml_singleton (STR ''first'') lpc_seg_child_parser id;
    second\<leftarrow>xml_singleton (STR ''second'') lpc_seg_child_parser id;
    fi\<leftarrow>xml_singleton (STR ''firstInput'') lpc_term_parser id;
    fo\<leftarrow>xml_singleton (STR ''firstOutput'') lpc_term_parser id;
    si\<leftarrow>xml_singleton (STR ''secondInput'') lpc_term_parser id;
    so\<leftarrow>xml_singleton (STR ''secondOutput'') lpc_term_parser id;
    final\<leftarrow>xml_singleton (STR ''finalOutput'') lpc_term_parser id;
    u\<leftarrow>xml_singleton (STR ''firstContinuation'') lpc_symbol_parser id;
    v\<leftarrow>xml_singleton (STR ''secondContinuation'') lpc_symbol_parser id;
    caps\<leftarrow>xml_many (STR ''captured'') lpc_term_parser id;
    more\<leftarrow>xml_many (STR ''moreCaptured'') lpc_term_parser id;
    first_evidence\<leftarrow>xml_singleton (STR ''prefixEvidence'') lpc_seg_ground_evidence_parser id;
    second_evidence\<leftarrow>xml_singleton (STR ''secondEvidence'') lpc_seg_ground_evidence_parser id;
    xml_return \<lparr>lpcss_pre = pre,lpcss_rest = rest,lpcss_ground = H,lpcss_first = first,lpcss_second = second,
      lpcss_first_in = fi,lpcss_first_out = fo,lpcss_second_in = si,lpcss_second_out = so,lpcss_final = final,
      lpcss_u = u,lpcss_v = v,lpcss_caps = caps,lpcss_more_caps = more,
      lpcss_prefix_evidence = first_evidence,lpcss_second_evidence = second_evidence\<rparr>}"

definition lpc_seg_component_parser where
  "lpc_seg_component_parser =
    (xml_change lpc_seg_region_parser (\<lambda>x. xml_return (LPCSEGRegion x))) XMLor
    (xml_change lpc_seg_split_parser (\<lambda>x. xml_return (LPCSEGSplit x)))"

definition lpc_seg_certificate_parser where
  "lpc_seg_certificate_parser = XMLdo (STR ''lpCutSEGTerminationProof'') {
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,bs)}) id;
    q\<leftarrow>xml_text (STR ''predicate'');
    modes\<leftarrow>xml_many (STR ''modes'') (xml_bool (STR ''mode'')) id;
    fuel\<leftarrow>xml_nat (STR ''fuel'');
    roots\<leftarrow>xml_many (STR ''roots'') lpc_seg_root_parser id;
    regions\<leftarrow>xml_many (STR ''regions'') lpc_seg_component_parser id;
    continuations\<leftarrow>xml_many (STR ''continuations'') lpc_symbol_parser id;
    controls\<leftarrow>lpc_seg_encoding_parser (STR ''controlEncoding'');
    data_map\<leftarrow>lpc_seg_encoding_parser (STR ''dataEncoding'');
    fallback\<leftarrow>xml_singleton (STR ''fallback'') symbol_parser id;
    constructors\<leftarrow>xml_many (STR ''constructors'') symbol_parser id;
    trs_rules\<leftarrow>CPF_Input_Parser.rules symbol_parser Mapping.empty Mapping.empty;
    prf\<leftarrow>xml2trs_termination_proof symbol_parser Mapping.empty Mapping.empty;
    xml_return (P,q,modes,fuel,roots,regions,continuations,controls,data_map,fallback,constructors,trs_rules,prf)}"

definition check_lpc_seg_certificate_xml where
  "check_lpc_seg_certificate_xml xml = (case parse_xml_string lpc_seg_certificate_parser xml of
    Right (P,q,modes,fuel,roots,regions,continuations,controls,data_map,fallback,constructors,trs_rules,prf) \<Rightarrow>
      check_lpc_seg_certificate tp_rbt_impl dpp_rbt_impl fuel P roots regions q modes
        continuations controls data_map fallback constructors trs_rules prf
    | _ \<Rightarrow> False)"

theorem check_lpc_seg_certificate_xml_sound:
  assumes parsed: "parse_xml_string lpc_seg_certificate_parser xml =
    Right (P,q,modes,fuel,roots,regions,continuations,controls,data_map,fallback,constructors,trs_rules,prf)"
    and ok: "check_lpc_seg_certificate_xml xml"
    and len: "length ts=length modes"
    and ground: "\<forall>(t,b)\<in>set (zip ts modes). b \<longrightarrow> lp_seg_ground t"
  shows "SN_on (lp_cut_mgu_source P) {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
  by (rule check_lpc_seg_certificate_sound[OF tp_rbt_impl dpp_rbt_impl _ len ground])
    (use parsed ok in \<open>simp add: check_lpc_seg_certificate_xml_def\<close>)

end
