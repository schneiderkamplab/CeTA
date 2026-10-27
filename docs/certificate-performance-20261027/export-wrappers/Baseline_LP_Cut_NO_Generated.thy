theory Baseline_LP_Cut_NO_Generated
imports "/work/dfm/festschrift/CeTA-consolidated/target/usable-membership-20261026/lp-source-committed/thys/Logic_Programming/LP_Cut_NO_XML"
begin
ML \<open>

val audited = [@{thm check_lpc_no_xml_sound}, @{thm lpc_no_resolve_swap_sound}];
val names = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = names [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof audited orelse
  exists (fn n => not (member (op =) inherited n)) (names audited)
  then error "Untrusted output-renaming NO certificate dependency" else ();
val (modules, _) = Code_Target.produce_code @{context} true
  [@{const_name check_lpc_no_xml}] "Haskell" "LP_Cut_NO_Generated" NONE [];

val root = Path.explode "/work/dfm/festschrift/CeTA-consolidated/target/certificate-performance-20261027/lp-baseline/LP_Cut_NO_Generated";
val _ = List.app (fn (names, bytes) => Bytes.write (root + Path.make names) bytes) modules;
val _ = writeln "EXPORTED_Baseline_LP_Cut_NO_Generated";
\<close>
end
