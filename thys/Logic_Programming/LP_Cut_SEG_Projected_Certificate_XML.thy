theory LP_Cut_SEG_Projected_Certificate_XML
  imports LP_Cut_SEG_Projected_Certificate LP_Cut_SEG_Free_Certificate_XML
begin

definition lpc_seg_projected_certificate_parser where
  "lpc_seg_projected_certificate_parser = XMLdo (STR ''lpCutSEGProjectedTerminationProof'') {
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,bs)}) id;
    q\<leftarrow>xml_text (STR ''predicate'');
    modes\<leftarrow>xml_many (STR ''modes'') (xml_bool (STR ''mode'')) id;
    fuel\<leftarrow>xml_nat (STR ''fuel'');
    roots\<leftarrow>xml_many (STR ''roots'') lpc_seg_root_parser id;
    Fs\<leftarrow>lpc_seg_free_sets_parser (STR ''rootFree'');
    regions\<leftarrow>xml_many (STR ''regions'') lpc_seg_free_component_parser id;
    continuations\<leftarrow>xml_many (STR ''continuations'') lpc_symbol_parser id;
    controls\<leftarrow>lpc_seg_encoding_parser (STR ''controlEncoding'');
    data_map\<leftarrow>lpc_seg_encoding_parser (STR ''dataEncoding'');
    fallback\<leftarrow>xml_singleton (STR ''fallback'') symbol_parser id;
    filters\<leftarrow>CPF_Proof_Parser.afs symbol_parser;
    trs_rules\<leftarrow>CPF_Input_Parser.rules symbol_parser Mapping.empty Mapping.empty;
    prf\<leftarrow>xml2trs_termination_proof symbol_parser Mapping.empty Mapping.empty;
    xml_return (P,q,modes,fuel,roots,Fs,regions,continuations,controls,data_map,fallback,filters,trs_rules,prf)}"

definition check_lpc_seg_projected_certificate_xml where
  "check_lpc_seg_projected_certificate_xml xml = (case parse_xml_string lpc_seg_projected_certificate_parser xml of
    Right (P,q,modes,fuel,roots,Fs,regions,continuations,controls,data_map,fallback,filters,trs_rules,prf) \<Rightarrow>
      check_lpc_seg_projected_certificate tp_rbt_impl dpp_rbt_impl fuel P roots Fs regions q modes
        continuations controls data_map fallback filters trs_rules prf
    | _ \<Rightarrow> False)"

theorem check_lpc_seg_projected_certificate_xml_sound:
  assumes parsed: "parse_xml_string lpc_seg_projected_certificate_parser xml =
    Right (P,q,modes,fuel,roots,Fs,regions,continuations,controls,data_map,fallback,filters,trs_rules,prf)"
    and ok: "check_lpc_seg_projected_certificate_xml xml"
    and len: "length ts=length modes"
    and ground: "\<forall>(t,b)\<in>set (zip ts modes). b \<longrightarrow> lp_seg_ground t"
  shows "SN_on (lp_cut_mgu_source P) {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
  by (rule check_lpc_seg_projected_certificate_sound[OF tp_rbt_impl dpp_rbt_impl _ len ground])
    (use parsed ok in \<open>simp add: check_lpc_seg_projected_certificate_xml_def\<close>)

end
