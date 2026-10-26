theory Baseline_LP_SEG_Projected_Generated
imports "/work/dfm/festschrift/CeTA-consolidated/target/usable-membership-20261026/lp-source-committed/thys/Logic_Programming/LP_Cut_SEG_Projected_Certificate_XML"
begin
ML \<open>
val (modules, _) = Code_Target.produce_code @{context} true [@{const_name check_lpc_seg_projected_certificate_xml}] "Haskell" "LP_SEG_Projected_Generated" NONE [];
val root = Path.explode "/work/dfm/festschrift/CeTA-consolidated/target/usable-membership-20261026/lp-baseline/LP_SEG_Projected_Generated";
val _ = List.app (fn (names, bytes) => Bytes.write (root + Path.make names) bytes) modules;
val _ = writeln "EXPORTED_Baseline_LP_SEG_Projected_Generated";
\<close>
end
