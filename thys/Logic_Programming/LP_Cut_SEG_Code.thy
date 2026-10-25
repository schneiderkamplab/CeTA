theory LP_Cut_SEG_Code
  imports LP_Cut_SEG_Certificate_XML LP_Cut_Return_Nested_XML
    LP_Constructor_XML LP_Source_Unify_XML LP_Cut_Constructor_XML LP_Cut_MGU_XML
begin

ML \<open>
val audited = [@{thm check_lpc_seg_certificate_xml_sound},
  @{thm check_lpc_return_nested_constructor_xml_sound}];
val names = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = names [@{thm check_trs_termination_proof}, @{thm check_lp_constructor_sound}];
val _ = if Thm_Deps.has_skip_proof audited orelse
  exists (fn n => not (member (op =) inherited n)) (names audited)
  then error "Untrusted LP certificate dependency" else ();
\<close>

export_code check_lpc_seg_certificate_xml
  in Haskell module_name LP_SEG_Certificate_Generated

export_code check_lpc_return_nested_constructor_xml
  check_lpc_return_composed_constructor_xml check_lpc_return_module_constructor_xml
  check_lpc_return_constructor_xml check_lpc_xml check_lpc_constructor_xml
  check_lpc_mgu_constructor_xml check_lp_constructor_any_xml check_lp_nontermination_all_xml
  in Haskell module_name LP_Return_Module_Generated

end
