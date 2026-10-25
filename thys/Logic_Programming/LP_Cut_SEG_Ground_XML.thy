theory LP_Cut_SEG_Ground_XML
  imports LP_Cut_SEG_Return_Bridge LP_Cut_SEG_Control_XML
begin

definition lpc_seg_ground_parser where
  "lpc_seg_ground_parser = XMLdo (STR ''lpCutSEGGround'') {
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,bs)}) id;
    pre\<leftarrow>xml_many (STR ''goals'') lpc_goal_parser id;
    G\<leftarrow>xml_many (STR ''ground'') (xml_text (STR ''var'')) id;
    vs\<leftarrow>xml_many (STR ''variables'') (xml_text (STR ''var'')) id;
    t\<leftarrow>xml_singleton (STR ''term'') lpc_term_parser id;
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
    xml_return (P,pre,G,vs,t,Q,Fs,modes)}"

definition check_lpc_seg_ground_xml where
  "check_lpc_seg_ground_xml xml = (case parse_xml_string lpc_seg_ground_parser xml of
    Right (P,pre,G,vs,t,Q,Fs,modes) \<Rightarrow>
      distinct vs \<and> vars_term t \<subseteq> set vs \<and>
      lpc_seg_check_return_ground P pre G vs t Q Fs modes
    | _ \<Rightarrow> False)"

end
