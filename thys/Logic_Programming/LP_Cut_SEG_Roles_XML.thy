theory LP_Cut_SEG_Roles_XML
  imports LP_Cut_SEG_Roles LP_Cut_SEG_Measure_XML
begin

definition lpc_seg_symbol_map_parser where
  "lpc_seg_symbol_map_parser tag = xml_many tag (XMLdo (STR ''mapping'') {
    a\<leftarrow>xml_singleton (STR ''source'') lpc_symbol_parser id;
    b\<leftarrow>xml_singleton (STR ''target'') lpc_symbol_parser id; xml_return (a,b)}) id"

definition lpc_seg_role_diagnostic_parser where
  "lpc_seg_role_diagnostic_parser = XMLdo (STR ''lpCutSEGRoles'') {
    controls\<leftarrow>lpc_seg_symbol_map_parser (STR ''controls'');
    continuations\<leftarrow>xml_many (STR ''continuations'') lpc_symbol_parser id;
    data_map\<leftarrow>lpc_seg_symbol_map_parser (STR ''dataMap'');
    fallback\<leftarrow>xml_singleton (STR ''fallback'') lpc_symbol_parser id;
    constructors\<leftarrow>xml_many (STR ''constructors'') lpc_symbol_parser id;
    trs_rules\<leftarrow>xml_many (STR ''rules'') (XMLdo (STR ''rule'') {
      l\<leftarrow>xml_singleton (STR ''lhs'') lpc_term_parser id;
      r\<leftarrow>xml_singleton (STR ''rhs'') lpc_term_parser id; xml_return (l,r)}) id;
    pair_entries\<leftarrow>xml_many (STR ''pairs'') (XMLdo (STR ''pair'') {
      nl\<leftarrow>xml_nat (STR ''leftDepth''); nr\<leftarrow>xml_nat (STR ''rightDepth'');
      l\<leftarrow>xml_singleton (STR ''lhs'') lpc_term_parser id;
      r\<leftarrow>xml_singleton (STR ''rhs'') lpc_term_parser id; xml_return (nl,nr,l,r)}) id;
    xml_return (controls,continuations,data_map,fallback,constructors,trs_rules,pair_entries)}"

definition check_lpc_seg_roles_xml where
  "check_lpc_seg_roles_xml xml = (case parse_xml_string lpc_seg_role_diagnostic_parser xml of
    Right (controls,continuations,data_map,fallback,constructors,trs_rules,pair_entries) \<Rightarrow>
      distinct (map fst controls) \<and> distinct (map fst data_map) \<and>
      List.member constructors fallback \<and>
      list_all (\<lambda>p. List.member constructors (snd p)) data_map \<and>
      list_all (\<lambda>(l,r). case l of Var x \<Rightarrow> False | Fun f ts \<Rightarrow>
        \<not> List.member constructors f) trs_rules \<and>
      length trs_rules=length pair_entries \<and>
      list_all (\<lambda>(nl,nr,l,r). lpc_seg_check_encoded_pair_list nl nr
        (List.member continuations) (lpc_lookup fallback controls)
        (lpc_lookup fallback data_map) constructors trs_rules l r) pair_entries
    | _ \<Rightarrow> False)"

end
