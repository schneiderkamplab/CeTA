theory LP_Prolog_Finite_Constructor_Triple_XML
  imports LP_Prolog_Finite_Triple_XML LP_Prolog_Finite_Constructor_Triple_Certificate LP_Dependency_Triple_Constructor_XML LP_Prolog_Constructor_Triple_XML
begin

definition lpp_established_finite_constructor_triples_parser where
  "lpp_established_finite_constructor_triples_parser = XMLdo (STR ''prologEstablishedFiniteSEGConstructorTriplesProof'') {
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
    child\<leftarrow>lp_triple_constructor_parser;
    xml_return (profile,P,q,modes,fuel,chain_pred,D,Q,transfer,contexts,roots,blocks,enc_pred,enc_data,child)}"

definition check_lpp_established_finite_constructor_triples_xml where
  "check_lpp_established_finite_constructor_triples_xml xml = (case parse_xml_string lpp_established_finite_constructor_triples_parser xml of
    Right (profile,P,q,modes,fuel,chain_pred,D,Q,(summaries,SP,receipts),contexts,roots,blocks,enc_pred,enc_data,
      (D',Q',outs,fallback,dnames,pnames,marks,filters,(q',n,positions),seed,nfs,prf)) \<Rightarrow>
      profile=''iso-rational-libraries-v1'' \<and>
      lpp_check_transfer_contract summaries SP receipts \<and>
      list_all (lpp_established_finite_component_header P fuel (summaries,SP,receipts)) blocks \<and>
      check_lpp_established_finite_constructor_triples tp_rbt_impl dpp_rbt_impl fuel P D Q (lpp_transfer_lookup summaries) roots contexts (map snd blocks) q modes chain_pred enc_pred enc_data
        D' Q' outs fallback dnames pnames marks filters q' n positions seed nfs prf
    | _ \<Rightarrow> False)"

theorem check_lpp_established_finite_constructor_triples_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpp_established_finite_constructor_triples_parser xml =
    Right (profile,P,q,modes,fuel,chain_pred,D,Q,(summaries,SP,receipts),contexts,roots,blocks,enc_pred,enc_data,
      (D',Q',outs,fallback,dnames,pnames,marks,filters,(q',n,positions),seed,nfs,prf))"
    and ok: "check_lpp_established_finite_constructor_triples_xml xml" and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature lpp_finite_source_builtin lpp_finite_source_domain)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
  by (rule check_lpp_established_finite_constructor_triples_sound[OF tp_rbt_impl dpp_rbt_impl _ _ len ground])
    (use parsed ok in \<open>auto simp: check_lpp_established_finite_constructor_triples_xml_def lpp_check_transfer_contract_def\<close>)

text \<open>Non-accepting diagnostics: parse, graph, exact child encoding,
child proof, then one Boolean for each source component.\<close>
definition lpp_established_finite_constructor_triples_diagnostics_xml where
  "lpp_established_finite_constructor_triples_diagnostics_xml xml = (case parse_xml_string lpp_established_finite_constructor_triples_parser xml of
    Right (profile,P,q,modes,fuel,chain_pred,D,Q,(summaries,SP,receipts),contexts,roots,blocks,enc_pred,enc_data,
      (D',Q',outs,fallback,dnames,pnames,marks,filters,(q',n,positions),seed,nfs,prf)) \<Rightarrow>
      [True,lpp_finite_triple_check_graph fuel P D Q (lpp_transfer_lookup summaries) roots contexts (map snd blocks) q modes chain_pred,
       D'=lp_roles_triples (lpc_lookup fallback enc_pred) (lpc_lookup fallback enc_data) D \<and>
       Q'=lp_roles_program (lpc_lookup fallback enc_pred) (lpc_lookup fallback enc_data) Q \<and>
       q'=lpc_lookup fallback enc_pred chain_pred \<and> n=length modes \<and> positions=lpc_positions modes,
       check_lp_triple_constructor tp_rbt_impl dpp_rbt_impl D' Q' outs fallback dnames pnames marks filters q' n positions seed nfs prf]
      @ map (\<lambda>i. lpp_finite_triple_check_component fuel P D Q (lpp_transfer_lookup summaries) roots contexts (contexts!i) (roots!i) (snd (blocks!i))) [0..<length roots]
    | _ \<Rightarrow> [False])"

ML \<open>
val checked = [@{thm check_lpp_established_finite_constructor_triples_xml_sound},
  @{thm lpp_finite_triple_graph_root_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted established source graph dependency" else ();
\<close>

end
