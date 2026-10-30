theory LP_Prolog_Context_ITS_XML
 imports LP_Prolog_Context_Regions LP_Prolog_Numeric_Component_XML
   LP_Prolog_Context_Module_XML LP_Cut_SEG_Triple_XML
begin

definition lpp_context_control_parser where
  "lpp_context_control_parser = XMLdo (STR ''prologContextControl'') {
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

definition lpp_context_region_parser where
  "lpp_context_region_parser = XMLdo (STR ''prologContextRegion'') {
    data\<leftarrow>lpp_context_control_parser;
    connections\<leftarrow>xml_many (STR ''connections'') lpc_triple_connection_parser id;
    xml_return (case data of (P,fuel,r,transfer,region) \<Rightarrow>
      (P,fuel,r,transfer,region\<lparr>lppcr_connections:=connections\<rparr>))}"

fun lpp_context_region_data where
  "lpp_context_region_data (P,fuel,r,transfer,region) = region"

fun lpp_check_context_region_data where
  "lpp_check_context_region_data P fuel transfer (P',fuel',r,transfer',region) =
    (P'=P \<and> fuel'=fuel \<and> r=0 \<and> transfer'=transfer)"

definition lpp_context_its_parser where
  "lpp_context_its_parser = XMLdo (STR ''prologContextITSProof'') {
    profile\<leftarrow>xml_text (STR ''profile'');
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,bs)}) id;
    q\<leftarrow>xml_text (STR ''predicate'');
    modes\<leftarrow>xml_many (STR ''modes'') (xml_bool (STR ''mode'')) id;
    fuel\<leftarrow>xml_nat (STR ''fuel'');
    roots\<leftarrow>xml_many (STR ''roots'') lpc_triple_root_parser id;
    regions\<leftarrow>xml_many (STR ''regions'') lpp_context_region_parser id;
    numeric\<leftarrow>lpp_numeric_component_parser;
    xml_return (profile,P,q,modes,fuel,roots,regions,numeric)}"

definition check_lpp_context_its_xml where
  "check_lpp_context_its_xml xml = (case parse_xml_string lpp_context_its_parser xml of
    Right (profile,P,q,modes,fuel,roots,regions,
      ((summaries,SP,receipts),coordinates,locations,D,row_data,system_impl,child_proof)) \<Rightarrow>
      profile=''iso-rational-libraries-v1'' \<and>
      distinct (map fst coordinates) \<and> distinct (map fst locations) \<and>
      lpp_check_transfer_contract summaries SP receipts \<and>
      list_all2 lpp_check_numeric_receipt_data D row_data \<and>
      lpp_check_numeric_component (lpp_transfer_lookup summaries)
        (lpp_numeric_coordinate_lookup coordinates) (lpp_numeric_location_lookup locations)
        system_impl D (map lpp_numeric_receipt_data row_data) child_proof \<and>
      list_all (lpp_check_context_region_data P fuel (summaries,SP,receipts)) regions \<and>
      lpp_check_context_regions_query fuel P D (lpp_transfer_lookup summaries) roots
        (map lpp_context_region_data regions) q modes
    | _ \<Rightarrow> False)"

theorem check_lpp_context_its_xml_sound:
  fixes ts :: "(string lp_cut_symbol,string) lp_iterm list"
  assumes parsed: "parse_xml_string lpp_context_its_parser xml =
    Right (profile,P,q,modes,fuel,roots,regions,
      ((summaries,SP,receipts),coordinates,locations,D,row_data,system_impl,child_proof))"
    and checked: "check_lpp_context_its_xml xml"
    and len: "length ts=length modes"
    and ground: "\<forall>(t,b)\<in>set (zip ts modes). b \<longrightarrow> lp_seg_ground t"
  shows "SN_on (lpp_domain_source P lpp_builtin_signature lpp_integer_source_builtin lpp_integer_source_domain)
    {[LPCGoals [LPCAtom (LPIFun (LPCUser q) ts)]]}"
proof -
  have transfer: "lpp_check_transfer_program (lpp_transfer_lookup summaries) SP receipts"
    and component: "lpp_check_numeric_component (lpp_transfer_lookup summaries)
      (lpp_numeric_coordinate_lookup coordinates) (lpp_numeric_location_lookup locations)
      system_impl D (map lpp_numeric_receipt_data row_data) child_proof"
    and source: "lpp_check_context_regions_query fuel P D (lpp_transfer_lookup summaries) roots
      (map lpp_context_region_data regions) q modes"
    using parsed checked by (auto simp: check_lpp_context_its_xml_def lpp_check_transfer_contract_def)
  have sn: "SN (lpp_observed_calls (set D) SP :: string lpp_success_iatom rel)"
    by (rule lpp_check_numeric_component_sound[OF component transfer])
  show ?thesis by (rule lpp_context_regions_query_sound[OF source transfer sn len ground])
qed

ML \<open>
val checked = [@{thm check_lpp_context_its_xml_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted contextual ITS source dependency" else ();
\<close>
end
