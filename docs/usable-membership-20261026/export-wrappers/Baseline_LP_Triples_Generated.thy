theory Baseline_LP_Triples_Generated
imports "/work/dfm/festschrift/CeTA-consolidated/target/usable-membership-20261026/lp-source-committed/thys/Logic_Programming/LP_Cut_Return_Triples_XML" "/work/dfm/festschrift/CeTA-consolidated/target/usable-membership-20261026/lp-source-committed/thys/Logic_Programming/LP_Cut_Return_Nested_Triples_XML" "/work/dfm/festschrift/CeTA-consolidated/target/usable-membership-20261026/lp-source-committed/thys/Logic_Programming/LP_Cut_Return_Composed_Triples_XML" "/work/dfm/festschrift/CeTA-consolidated/target/usable-membership-20261026/lp-source-committed/thys/Logic_Programming/LP_Cut_Return_Module_Triples_XML" "/work/dfm/festschrift/CeTA-consolidated/target/usable-membership-20261026/lp-source-committed/thys/Logic_Programming/LP_Cut_SEG_Triple_XML"
begin
ML \<open>
val (modules, _) = Code_Target.produce_code @{context} true [@{const_name check_lp_triple_pidp_xml}, @{const_name check_lp_initial_triples_xml},
   @{const_name check_lpc_return_triples_xml}, @{const_name check_lpc_return_nested_triples_xml},
   @{const_name check_lpc_return_composed_triples_xml}, @{const_name check_lpc_return_module_triples_xml}, @{const_name check_lpc_seg_triples_xml},
   @{const_name lpc_seg_triples_diagnostics_xml}] "Haskell" "LP_Triples_Generated" NONE [];
val root = Path.explode "/work/dfm/festschrift/CeTA-consolidated/target/usable-membership-20261026/lp-baseline/LP_Triples_Generated";
val _ = List.app (fn (names, bytes) => Bytes.write (root + Path.make names) bytes) modules;
val _ = writeln "EXPORTED_Baseline_LP_Triples_Generated";
\<close>
end
