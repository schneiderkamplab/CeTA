theory LP_Cut_SEG_Instance_XML
  imports LP_Cut_SEG_Instance LP_Cut_Return_Module_XML
begin

definition lpc_seg_instance_parser where
  "lpc_seg_instance_parser = XMLdo (STR ''lpCutSEGInstance'') {
    nd\<leftarrow>xml_singleton (STR ''source'') lpc_node_parser id;
    ss\<leftarrow>lpc_return_state_parser;
    child\<leftarrow>xml_singleton (STR ''child'') lpc_node_parser id;
    bindings\<leftarrow>lpc_bindings_parser;
    swaps\<leftarrow>xml_many (STR ''swaps'') (xml_pair (STR ''swap'')
      (xml_nat (STR ''scope'')) (xml_nat (STR ''scope'')) Pair) id;
    xml_return (nd,ss,child,bindings,swaps)}"

definition check_lpc_seg_instance_xml where
  "check_lpc_seg_instance_xml xml = (case parse_xml_string lpc_seg_instance_parser xml of
    Right (nd,[(e,observed)],child,bindings,swaps) \<Rightarrow>
      lpcn_state nd=[e] \<and> (case lpcn_state child of [ce] \<Rightarrow>
        lpc_seg_check_instance_boundary e (lpcn_ground nd) (lpcn_guards nd) (lpcn_vars nd) observed
          ce (lpcn_ground child) (lpcn_guards child) (lpcn_vars child) bindings swaps
        | _ \<Rightarrow> False)
    | _ \<Rightarrow> False)"

end
