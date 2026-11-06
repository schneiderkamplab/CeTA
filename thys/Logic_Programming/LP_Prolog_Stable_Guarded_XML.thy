theory LP_Prolog_Stable_Guarded_XML
 imports LP_Prolog_Stable_Numeric_XML LP_Prolog_Finite_Guarded_XML
begin

definition lpp_established_stable_guarded_parser where
  "lpp_established_stable_guarded_parser = XMLdo (STR ''prologEstablishedStableSEGGuardedProof'') {
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
    OD\<leftarrow>xml_many (STR ''observedTriples'') lpp_observed_triple_parser id;
    descents\<leftarrow>xml_many (STR ''guardedDescents'') lpp_finite_guarded_descent_parser id;
    projections\<leftarrow>xml_many (STR ''argumentProjection'') (XMLdo (STR ''entry'') {
      p\<leftarrow>xml_text (STR ''predicate'');
      positions\<leftarrow>xml_many (STR ''positions'') (xml_nat (STR ''position'')) id;
      xml_return (p,positions)}) id;
    child\<leftarrow>lpp_stable_numeric_component_parser;
    xml_return (profile,P,q,modes,fuel,chain_pred,D,Q,transfer,contexts,roots,blocks,OD,descents,projections,child)}"

definition check_lpp_established_stable_guarded_xml where
  "check_lpp_established_stable_guarded_xml xml = (case parse_xml_string lpp_established_stable_guarded_parser xml of
    Right (profile,P,q,modes,fuel,chain_pred,D,Q,(summaries,SP,receipts),contexts,roots,blocks,OD,descents,projections,
      (child_transfer,coordinates,coordinate_modes,locations,child_D,row_data,system_impl,child_proof)) \<Rightarrow>
      (let positions=lpp_numeric_coordinate_lookup projections in
       profile=''iso-rational-libraries-v1'' \<and>
       lpp_check_transfer_contract summaries SP receipts \<and>
       list_all (lpp_established_finite_component_header P fuel (summaries,SP,receipts)) blocks \<and>
       child_transfer=(summaries,SP,receipts) \<and>
       distinct (map fst projections) \<and> distinct (map fst coordinates) \<and> distinct (map fst coordinate_modes) \<and> distinct (map fst locations) \<and>
       list_all (\<lambda>((h,ps,b,gs),os). fst h\<in>set (map fst projections) \<and> fst b\<in>set (map fst projections)) OD \<and>
       child_D=map (lpp_project_observed_triple positions) OD \<and>
       lpp_check_stable_guarded_numeric_graph fuel P D Q (lpp_transfer_lookup summaries) SP receipts
         roots contexts (map snd blocks) q modes chain_pred OD descents positions
         (lpp_numeric_coordinate_lookup coordinates) (lpp_numeric_coordinate_lookup coordinate_modes) (lpp_numeric_location_lookup locations)
         system_impl row_data child_proof)
    | _ \<Rightarrow> False)"


theorem check_lpp_established_stable_guarded_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) term list"
  assumes parsed: "parse_xml_string lpp_established_stable_guarded_parser xml =
    Right (profile,P,q,modes,fuel,chain_pred,D,Q,(summaries,SP,receipts),contexts,roots,blocks,OD,descents,projections,
      (child_transfer,coordinates,coordinate_modes,locations,child_D,row_data,system_impl,child_proof))"
    and ok: "check_lpp_established_stable_guarded_xml xml"
    and len: "length ts=length modes"
    and ground: "\<And>i. i\<in>set (lpc_positions modes) \<Longrightarrow> ground (ts!i)"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature (lpp_stable_source_builtin (lpp_stable_profile_operation fallback)) lpp_finite_source_domain)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) ts))]]}"
proof -
  have checked: "lpp_check_stable_guarded_numeric_graph fuel P D Q (lpp_transfer_lookup summaries) SP receipts
      roots contexts (map snd blocks) q modes chain_pred OD descents (lpp_numeric_coordinate_lookup projections)
      (lpp_numeric_coordinate_lookup coordinates) (lpp_numeric_coordinate_lookup coordinate_modes) (lpp_numeric_location_lookup locations)
      system_impl row_data child_proof"
    using parsed ok by (auto simp: check_lpp_established_stable_guarded_xml_def Let_def)
  show ?thesis
  proof (rule lpp_check_profile_guarded_numeric_graph_sound[OF checked])
    show "length (map (\<lambda>t. lp_ieval t LPIVar) ts)=length modes" using len by simp
    show "\<forall>(t,b)\<in>set (zip (map (\<lambda>t. lp_ieval t LPIVar) ts) modes). b \<longrightarrow> lp_seg_ground t"
      using ground len
      by (auto simp: in_set_zip lpc_positions_def lp_seg_ground_eval ground_vars_term_empty)
  qed
qed

ML \<open>
val checked = [@{thm check_lpp_established_stable_guarded_xml_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted stable source XML dependency" else ();
\<close>
end
