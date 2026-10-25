theory LP_Cut_SEG_Measure_XML
  imports LP_Cut_SEG_Control_XML LP_Cut_SEG_Measure
begin

definition lpc_seg_templates_parser where
  "lpc_seg_templates_parser = xml_many (STR ''templates'') (XMLdo (STR ''template'') {
    f\<leftarrow>xml_singleton (STR ''symbol'') lpc_symbol_parser id;
    vs\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
    t\<leftarrow>xml_singleton (STR ''term'') lpc_term_parser id;
    xml_return (f,vs,t)}) id"

definition lpc_seg_measure_diagnostic_parser where
  "lpc_seg_measure_diagnostic_parser = XMLdo (STR ''lpCutSEGMeasure'') {
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,bs)}) id;
    fuel\<leftarrow>xml_nat (STR ''fuel''); data\<leftarrow>lpc_seg_control_parser;
    templates\<leftarrow>lpc_seg_templates_parser;
    xml_return (P,fuel,data,templates)}"

definition check_lpc_seg_measure_xml where
  "check_lpc_seg_measure_xml xml = (case parse_xml_string lpc_seg_measure_diagnostic_parser xml of
    Right (P,fuel,data,templates) \<Rightarrow> lpc_seg_control_data_check fuel P data \<and>
      lpc_seg_check_templates templates (lpcsc_program data) | _ \<Rightarrow> False)"

end
