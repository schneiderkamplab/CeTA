theory LP_Prolog_Separation_Subject_XML
 imports LP_Prolog_Separation_Action_XML
begin

definition lpp_separation_subject_parser where
 "lpp_separation_subject_parser = XMLdo (STR ''separationSubject'') {
    P\<leftarrow>xml_many (STR ''program'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_term_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_goal_parser id; xml_return (h,bs)}) id;
    Q\<leftarrow>xml_many (STR ''residual'') (XMLdo (STR ''clause'') {
      h\<leftarrow>xml_singleton (STR ''head'') lpc_atom_parser id;
      bs\<leftarrow>xml_many (STR ''body'') lpc_atom_parser id; xml_return (h,bs)}) id;
    xml_return (P,Q)}"

definition lpp_decode_separation_subject where
 "lpp_decode_separation_subject xml = parse_xml_string lpp_separation_subject_parser xml"

text \<open>This parser binds local program and residual subjects only. Source
profile/query initialization, module contracts and residual proofs are separate.\<close>
end
