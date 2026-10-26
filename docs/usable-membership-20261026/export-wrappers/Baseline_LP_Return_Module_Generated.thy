theory Baseline_LP_Return_Module_Generated
imports "/work/dfm/festschrift/CeTA-consolidated/target/usable-membership-20261026/lp-source-committed/thys/Logic_Programming/LP_Cut_Return_Nested_XML" "/work/dfm/festschrift/CeTA-consolidated/target/usable-membership-20261026/lp-source-committed/thys/Logic_Programming/LP_Constructor_XML" "/work/dfm/festschrift/CeTA-consolidated/target/usable-membership-20261026/lp-source-committed/thys/Logic_Programming/LP_Source_Unify_XML" "/work/dfm/festschrift/CeTA-consolidated/target/usable-membership-20261026/lp-source-committed/thys/Logic_Programming/LP_Cut_Constructor_XML" "/work/dfm/festschrift/CeTA-consolidated/target/usable-membership-20261026/lp-source-committed/thys/Logic_Programming/LP_Cut_MGU_XML"
begin
ML \<open>
val (modules, _) = Code_Target.produce_code @{context} true [@{const_name check_lpc_return_nested_constructor_xml}, @{const_name check_lp_constructor_any_xml}, @{const_name check_lp_nontermination_all_xml},
   @{const_name check_lpc_xml}, @{const_name check_lpc_constructor_xml},
   @{const_name check_lpc_mgu_constructor_xml}, @{const_name lpc_xml_diagnostics},
   @{const_name check_lpc_return_composed_constructor_xml}, @{const_name check_lpc_return_composed_table_xml},
   @{const_name check_lpc_return_module_constructor_xml}, @{const_name check_lpc_return_constructor_xml},
   @{const_name check_lpc_return_module_table_xml}, @{const_name check_lpc_return_table_xml}] "Haskell" "LP_Return_Module_Generated" NONE [];
val root = Path.explode "/work/dfm/festschrift/CeTA-consolidated/target/usable-membership-20261026/lp-baseline/LP_Return_Module_Generated";
val _ = List.app (fn (names, bytes) => Bytes.write (root + Path.make names) bytes) modules;
val _ = writeln "EXPORTED_Baseline_LP_Return_Module_Generated";
\<close>
end
