theory LP_Prolog_Stable_Mixed_XML
 imports LP_Prolog_Stable_Backend_XML LP_Prolog_Stable_Mixed_Code_Setup
begin

definition lpp_mixed_backend_parser where
  "lpp_mixed_backend_parser =
    (xml_change lpp_structural_backend_parser (\<lambda>x. xml_return (Inl x))) XMLor
    (xml_change lpp_numeric_backend_parser (\<lambda>x. xml_return (Inr x)))"

fun lpp_decode_mixed_backend where
  "lpp_decode_mixed_backend transfer source_rows (Inl data) =
    map_option Inl (lpp_decode_structural_backend (fst (snd transfer)) data)"
| "lpp_decode_mixed_backend transfer source_rows (Inr data) =
    map_option Inr (lpp_decode_numeric_backend transfer source_rows data)"

definition lpp_mixed_rank_lookup where
  "lpp_mixed_rank_lookup ranks p = the_default 0 (map_of ranks p)"

definition lpp_decode_mixed_backends where
  "lpp_decode_mixed_backends transfer OD ranks raw = map (\<lambda>n.
    lpp_decode_mixed_backend transfer (lpp_stable_rank_row_list (lpp_mixed_rank_lookup ranks) n OD) (raw!n))
      [0..<length raw]"

definition lpp_established_stable_mixed_parser where
  "lpp_established_stable_mixed_parser = XMLdo (STR ''prologEstablishedStableSEGMixedProof'') {
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
    blocks\<leftarrow>xml_many (STR ''components'') lpp_relational_component_parser id;
    OD\<leftarrow>xml_many (STR ''observedTriples'') lpp_observed_triple_parser id;
    ranks\<leftarrow>xml_many (STR ''routing'') (XMLdo (STR ''entry'') {
      p\<leftarrow>xml_text (STR ''predicate''); n\<leftarrow>xml_nat (STR ''rank''); xml_return (p,n)}) id;
    backends\<leftarrow>xml_many (STR ''backends'') lpp_mixed_backend_parser id;
    xml_return (profile,P,q,modes,fuel,chain_pred,D,Q,transfer,contexts,roots,blocks,OD,ranks,backends)}"

definition check_lpp_established_stable_mixed_xml where
  "check_lpp_established_stable_mixed_xml xml = (case parse_xml_string lpp_established_stable_mixed_parser xml of
    Right (profile,P,q,modes,fuel,chain_pred,D,Q,(summaries,SP,receipts),contexts,roots,blocks,OD,ranks,raw) \<Rightarrow>
      (let candidates=lpp_decode_mixed_backends (summaries,SP,receipts) OD ranks raw in
        profile=''iso-rational-libraries-v1'' \<and>
        lpp_check_transfer_contract summaries SP receipts \<and>
        list_all (lpp_relational_component_header P fuel (summaries,SP,receipts)) blocks \<and>
        distinct (map fst ranks) \<and>
        list_all (\<lambda>((h,ps,b,gs),os). fst h\<in>set (map fst ranks) \<and> fst b\<in>set (map fst ranks)) OD \<and>
        list_all (\<lambda>candidate. case candidate of None \<Rightarrow> False | Some _ \<Rightarrow> True) candidates \<and>
        lpp_check_stable_mixed_graph tp_rbt_impl dpp_rbt_impl fuel P D Q (lpp_transfer_lookup summaries) SP receipts
          roots contexts (map snd blocks) q modes chain_pred OD (lpp_mixed_rank_lookup ranks) (map the candidates))
    | _ \<Rightarrow> False)"

theorem check_lpp_established_stable_mixed_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpp_established_stable_mixed_parser xml =
    Right (profile,P,q,modes,fuel,chain_pred,D,Q,(summaries,SP,receipts),contexts,roots,blocks,OD,ranks,raw)"
    and ok: "check_lpp_established_stable_mixed_xml xml"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature (lpp_stable_source_builtin (lpp_stable_profile_operation fallback)) lpp_finite_source_domain)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof -
  have checked: "lpp_check_stable_mixed_graph tp_rbt_impl dpp_rbt_impl fuel P D Q (lpp_transfer_lookup summaries) SP receipts
      roots contexts (map snd blocks) q modes chain_pred OD (lpp_mixed_rank_lookup ranks)
      (map the (lpp_decode_mixed_backends (summaries,SP,receipts) OD ranks raw))"
    using parsed ok by (auto simp: check_lpp_established_stable_mixed_xml_def Let_def)
  show ?thesis
  proof (rule lpp_check_profile_mixed_graph_sound[OF tp_rbt_impl dpp_rbt_impl checked])
    show "length (map (\<lambda>t. lp_ieval t LPIVar) ts)=length modes" using len by simp
    show "\<forall>(t,b)\<in>set (zip (map (\<lambda>t. lp_ieval t LPIVar) ts) modes). b \<longrightarrow> lp_seg_ground t"
      using ground len by (auto simp: in_set_zip lpc_positions_def lp_seg_ground_eval ground_vars_term_empty)
  qed
qed

ML \<open>
val checked = [@{thm check_lpp_established_stable_mixed_xml_sound}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (map (fst o fst) (Thm_Deps.all_oracles checked))
  then error "Untrusted mixed source XML" else ();
\<close>
end
