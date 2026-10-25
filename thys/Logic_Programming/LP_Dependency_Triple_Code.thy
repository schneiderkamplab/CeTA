theory LP_Dependency_Triple_Code
  imports LP_Cut_Return_Triples_XML LP_Cut_Return_Nested_Triples_XML
    LP_Cut_Return_Composed_Triples_XML LP_Cut_Return_Module_Triples_XML
    LP_Cut_SEG_Triple_XML
begin

ML \<open>
val audited = [@{thm check_lp_triple_pidp_xml_sound},
  @{thm check_lp_initial_triples_xml_sound}, @{thm check_lpc_return_triples_xml_sound},
  @{thm check_lpc_return_nested_triples_xml_sound},
  @{thm check_lpc_return_composed_triples_xml_sound},
  @{thm check_lpc_return_module_triples_xml_sound},
  @{thm check_lpc_seg_triples_xml_sound}];
val names = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = names [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof audited orelse
  exists (fn n => not (member (op =) inherited n)) (names audited)
  then error "Untrusted dependency-triples certificate dependency" else ();
\<close>

export_code check_lp_triple_pidp_xml check_lp_initial_triples_xml
  check_lpc_return_triples_xml check_lpc_return_nested_triples_xml
  check_lpc_return_composed_triples_xml check_lpc_return_module_triples_xml
  check_lpc_seg_triples_xml lpc_seg_triples_diagnostics_xml
  in Haskell module_name LP_Triples_Generated

end
