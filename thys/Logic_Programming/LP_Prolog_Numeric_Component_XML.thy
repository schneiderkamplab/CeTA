theory LP_Prolog_Numeric_Component_XML
 imports LP_Prolog_Numeric_Component LP_Prolog_Numeric_Code_Setup
   LP_Prolog_Numeric_Path_XML LP_Prolog_Success_Transfer_XML ITS_Ext.IA4_Parser
begin

definition lpp_observed_triple_parser where
  "lpp_observed_triple_parser = XMLdo (STR ''triple'') {
    h\<leftarrow>xml_singleton (STR ''head'') lpp_success_atom_parser id;
    ps\<leftarrow>xml_many (STR ''prefix'') lpp_success_atom_parser id;
    b\<leftarrow>xml_singleton (STR ''call'') lpp_success_atom_parser id;
    gs\<leftarrow>xml_many (STR ''guards'') lpp_success_guard_parser id;
    os\<leftarrow>xml_many (STR ''observations'')
      ((xml_singleton (STR ''integerGuard'') lpc_term_parser LPPOInteger) XMLor lpp_numeric_observation_parser) id;
    xml_return ((h,ps,b,gs),os)}"

definition lpp_numeric_call_receipt_parser where
  "lpp_numeric_call_receipt_parser = XMLdo (STR ''row'') {
    facts\<leftarrow>xml_many (STR ''facts'') lpp_transfer_fact_parser id;
    path\<leftarrow>lpp_numeric_path_parser;
    xml_return (facts,path)}"

definition lpp_numeric_coordinate_lookup where
  "lpp_numeric_coordinate_lookup coordinates p = (case map_of coordinates p of None\<Rightarrow>[] | Some xs\<Rightarrow>xs)"
definition lpp_numeric_location_lookup where
  "lpp_numeric_location_lookup locations p = (case map_of locations p of None\<Rightarrow>'''' | Some loc\<Rightarrow>loc)"

definition lpp_numeric_component_parser where
  "lpp_numeric_component_parser = XMLdo (STR ''prologNumericComponent'') {
    transfer\<leftarrow>lpp_transfer_contract_parser;
    coordinates\<leftarrow>xml_many (STR ''coordinates'') (XMLdo (STR ''entry'') {
      p\<leftarrow>xml_text (STR ''predicate'');
      vs\<leftarrow>xml_many (STR ''names'') (xml_text (STR ''coordinate'')) id;
      xml_return (p,vs)}) id;
    locations\<leftarrow>xml_many (STR ''locations'') (XMLdo (STR ''entry'') {
      p\<leftarrow>xml_text (STR ''predicate''); loc\<leftarrow>xml_text (STR ''locationId'');
      xml_return (p,loc)}) id;
    triples\<leftarrow>xml_many (STR ''triples'') lpp_observed_triple_parser id;
    row_data\<leftarrow>xml_many (STR ''rows'') lpp_numeric_call_receipt_parser id;
    system_impl\<leftarrow>ia4_lts_input_parser;
    child_proof\<leftarrow>xml_singleton (STR ''ltsTerminationProof'')
      (ia4_lts_termination_proof_parser :: (ia4_sig,string,IA.ty,string,string,la_solver_type) termination_proof xmlt) id;
    xml_return (transfer,coordinates,locations,triples,row_data,system_impl,child_proof)}"

fun lpp_numeric_receipt_data where
  "lpp_numeric_receipt_data (facts,(K,inputs,outputs,observations,tests,bindings,formula)) =
    \<lparr>lppnc_facts=facts,lppnc_inputs=inputs,lppnc_outputs= outputs,lppnc_tests=tests,
      lppnc_bindings=bindings,lppnc_formula=formula\<rparr>"

fun lpp_check_numeric_receipt_data where
  "lpp_check_numeric_receipt_data ((h,ps,b,gs),os)
    (facts,(K,inputs,outputs,observations,tests,bindings,formula)) =
    (set K=set (map lpp_transfer_variable facts) \<and>
      observations=filter lpp_numeric_constraint_observation os)"

definition check_lpp_numeric_component_xml where
  "check_lpp_numeric_component_xml xml = (case parse_xml_string lpp_numeric_component_parser xml of
    Right ((summaries,P,receipts),coordinates,locations,D,row_data,system_impl,child_proof) \<Rightarrow>
      distinct (map fst coordinates) \<and> distinct (map fst locations) \<and>
      lpp_check_transfer_contract summaries P receipts \<and>
      list_all2 lpp_check_numeric_receipt_data D row_data \<and>
      lpp_check_numeric_component (lpp_transfer_lookup summaries)
        (lpp_numeric_coordinate_lookup coordinates) (lpp_numeric_location_lookup locations)
        system_impl D (map lpp_numeric_receipt_data row_data) child_proof
    | _ \<Rightarrow> False)"

theorem check_lpp_numeric_component_xml_sound:
  assumes parsed: "parse_xml_string lpp_numeric_component_parser xml =
    Right ((summaries,P,receipts),coordinates,locations,D,row_data,system_impl,child_proof)"
    and checked: "check_lpp_numeric_component_xml xml"
  shows "SN (lpp_observed_calls (set D) P)"
  by (rule lpp_check_numeric_component_sound[where
    T="lpp_transfer_lookup summaries" and coordinates="lpp_numeric_coordinate_lookup coordinates"
    and locations="lpp_numeric_location_lookup locations" and system_impl=system_impl
    and row_receipts="map lpp_numeric_receipt_data row_data" and child_proof=child_proof and receipts=receipts])
    (use parsed checked in \<open>auto simp: check_lpp_numeric_component_xml_def lpp_check_transfer_contract_def\<close>)

text \<open>This parser certifies a residual component only. Its complete call
relation and success program must be bound to the source graph before a source
termination verdict is authorized.\<close>
end
