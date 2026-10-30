theory LP_Prolog_Guarded_Backends
  imports LP_Prolog_Guarded_Triples LP_Prolog_Numeric_Guards LP_Prolog_Success_Transfer_XML LP_Prolog_Integer_Node_Domain LP_Prolog_Numeric_Row_XML
    LP_Prolog_Observed_Calls LP_Prolog_Guarded_Returns LP_Prolog_Numeric_Path_XML LP_Prolog_Numeric_Valuation LP_Prolog_Integer_Legacy LP_Prolog_Context_Module_XML
begin

text \<open>Combined backend components. These check successful-prefix type
contracts, integer primitive semantics and numeric guard lowering. Source
certification additionally requires complete SEG reconstruction and the typed
SCC/backend assembly; importing these components alone authorizes no verdict.\<close>

ML \<open>
val source_node_theorems = [@{thm check_lpp_context_module_xml_domain_SN}, @{thm check_lpp_context_module_xml_contract}, @{thm lpp_check_context_module_contract}, @{thm lpp_integer_is_node_sound}, @{thm lpp_integer_test_node_sound},
  @{thm lpp_integer_comparison_node_sound}, @{thm lpp_context_is_node_sound},
  @{thm lpp_context_comparison_sound}, @{thm lpp_context_integer_test_sound}];
val source_node_oracles = map (fst o fst) o Thm_Deps.all_oracles;
val source_node_inherited = source_node_oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof source_node_theorems orelse
  exists (fn n => not (member (op =) source_node_inherited n)) (source_node_oracles source_node_theorems)
  then error "Untrusted integer source-node dependency" else ();
\<close>
end
