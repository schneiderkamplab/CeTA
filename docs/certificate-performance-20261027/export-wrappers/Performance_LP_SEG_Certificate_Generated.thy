theory Performance_LP_SEG_Certificate_Generated
imports "/work/dfm/festschrift/CeTA-consolidated/target/usable-membership-20261026/lp-source-committed/thys/Logic_Programming/LP_Cut_SEG_Free_Certificate_XML" "/work/dfm/festschrift/CeTA-consolidated/thys/Usable_Rules_Membership/Usable_Rules_Membership" "/work/dfm/festschrift/CeTA-consolidated/thys/Certificate_Performance/Certificate_Performance"
begin
ML \<open>

val audited = [@{thm check_lpc_seg_free_certificate_xml_sound}, @{thm check_lpc_seg_certificate_xml_sound}, @{thm check_trs_termination_proof}, @{thm check_ur_closed_term_set_eq}, @{thm check_ur_P_closed_rm_af_indexed_code}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val used = map (fst o fst) (Thm_Deps.all_oracles audited);
val _ = if Thm_Deps.has_skip_proof audited orelse exists (fn n => not (member (op =) inherited n)) used then error "Untrusted indexed LP export" else ();
val (modules, _) = Code_Target.produce_code @{context} true [@{const_name check_lpc_seg_free_certificate_xml}, @{const_name check_lpc_seg_certificate_xml}] "Haskell" "LP_SEG_Certificate_Generated" NONE [];

val root = Path.explode "/work/dfm/festschrift/CeTA-consolidated/target/certificate-performance-20261027/lp-performance/LP_SEG_Certificate_Generated";
val _ = List.app (fn (names, bytes) => Bytes.write (root + Path.make names) bytes) modules;
val _ = writeln "EXPORTED_Performance_LP_SEG_Certificate_Generated";
\<close>
end
