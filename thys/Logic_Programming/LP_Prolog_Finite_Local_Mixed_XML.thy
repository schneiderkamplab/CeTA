theory LP_Prolog_Finite_Local_Mixed_XML
 imports LP_Prolog_Finite_Local_Mixed_Graph LP_Prolog_Stable_Mixed_XML
begin

definition lpp_established_finite_local_mixed_parser where
  "lpp_established_finite_local_mixed_parser = XMLdo (STR ''prologEstablishedFiniteLocalSEGMixedProof'') {
    profile\<leftarrow>xml_text (STR ''profile'');
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,bs)}) id;
    q\<leftarrow>xml_text (STR ''predicate'');
    modes\<leftarrow>xml_many (STR ''modes'') (xml_bool (STR ''mode'')) id;
    signatures\<leftarrow>xml_many (STR ''signatures'') (XMLdo (STR ''signature'') {
      f\<leftarrow>xml_text (STR ''predicate''); n\<leftarrow>xml_nat (STR ''arity''); xml_return (f,n)}) id;
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
    OD\<leftarrow>xml_many (STR ''observedTriples'') lpp_observed_triple_parser id;
    descents\<leftarrow>xml_many (STR ''guardedDescents'') lpp_finite_guarded_descent_parser id;
    ranks\<leftarrow>xml_many (STR ''routing'') (XMLdo (STR ''entry'') {
      p\<leftarrow>xml_text (STR ''predicate''); n\<leftarrow>xml_nat (STR ''rank''); xml_return (p,n)}) id;
    backends\<leftarrow>xml_many (STR ''backends'') lpp_mixed_backend_parser id;
    xml_return (profile,P,q,modes,signatures,fuel,chain_pred,D,Q,transfer,contexts,roots,blocks,OD,descents,ranks,backends)}"

definition check_lpp_established_finite_local_mixed_xml where
  "check_lpp_established_finite_local_mixed_xml xml = (case parse_xml_string lpp_established_finite_local_mixed_parser xml of
    Right (profile,P,q,modes,signatures,fuel,chain_pred,D,Q,(summaries,SP,receipts),contexts,roots,blocks,OD,descents,ranks,raw) \<Rightarrow>
      (let candidates=lpp_decode_mixed_backends (summaries,SP,receipts) OD ranks raw in
        profile=''iso-rational-libraries-v1'' \<and>
        lpp_check_transfer_contract summaries SP receipts \<and>
        list_all (lpp_established_finite_component_header P fuel (summaries,SP,receipts)) blocks \<and>
        distinct (map fst ranks) \<and>
        list_all (\<lambda>((h,ps,b,gs),os). fst h\<in>set (map fst ranks) \<and> fst b\<in>set (map fst ranks)) OD \<and>
        list_all (\<lambda>candidate. case candidate of None \<Rightarrow> False | Some _ \<Rightarrow> True) candidates \<and>
        lpp_check_finite_local_mixed_graph tp_rbt_impl dpp_rbt_impl (set signatures) fuel P D Q (lpp_transfer_lookup summaries) SP receipts
          roots contexts (map snd blocks) q modes chain_pred OD descents (lpp_mixed_rank_lookup ranks) (map the candidates))
    | _ \<Rightarrow> False)"

theorem check_lpp_established_finite_local_mixed_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpp_established_finite_local_mixed_parser xml =
    Right (profile,P,q,modes,signatures,fuel,chain_pred,D,Q,(summaries,SP,receipts),contexts,roots,blocks,OD,descents,ranks,raw)"
    and ok: "check_lpp_established_finite_local_mixed_xml xml"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature (lpp_stable_source_builtin (lpp_stable_profile_operation fallback)) lpp_finite_source_domain)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof -
  have checked: "lpp_check_finite_local_mixed_graph tp_rbt_impl dpp_rbt_impl (set signatures) fuel P D Q (lpp_transfer_lookup summaries) SP receipts
      roots contexts (map snd blocks) q modes chain_pred OD descents (lpp_mixed_rank_lookup ranks)
      (map the (lpp_decode_mixed_backends (summaries,SP,receipts) OD ranks raw))"
    using parsed ok by (auto simp: check_lpp_established_finite_local_mixed_xml_def Let_def)
  show ?thesis
  proof (rule lpp_check_finite_local_mixed_graph_sound[OF tp_rbt_impl dpp_rbt_impl lpp_stable_profile_integer_compatible checked])
    show "list_all lpp_finite_term (map (\<lambda>t. lp_ieval t LPIVar) ts)"
      by (auto simp: list_all_iff intro: lpp_finite_term_eval)
    show "length (map (\<lambda>t. lp_ieval t LPIVar) ts)=length modes" using len by simp
    show "\<forall>(t,b)\<in>set (zip (map (\<lambda>t. lp_ieval t LPIVar) ts) modes). b \<longrightarrow> lp_seg_ground t"
      using ground len by (auto simp: in_set_zip lpc_positions_def lp_seg_ground_eval ground_vars_term_empty)
  qed
qed

ML \<open>
val checked = [@{thm check_lpp_established_finite_local_mixed_xml_sound}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles checked))
  then error "Untrusted mixed source XML" else ();
\<close>
end
