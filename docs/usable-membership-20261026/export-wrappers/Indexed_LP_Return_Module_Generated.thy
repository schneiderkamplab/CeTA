theory Indexed_LP_Return_Module_Generated
imports "/work/dfm/festschrift/CeTA-consolidated/target/usable-membership-20261026/lp-wrappers/Baseline_LP_Return_Module_Generated" "/work/dfm/festschrift/CeTA-consolidated/thys/Usable_Rules_Membership/Usable_Rules_Membership"
begin
ML \<open>
val audited = [@{thm check_lpc_return_nested_constructor_xml_sound}, @{thm check_lpc_return_composed_constructor_xml_sound}, @{thm check_lp_constructor_sound}, @{thm lpc_actual_return_preserves_ground_env}, @{thm check_ur_closed_term_set_eq}, @{thm check_ur_P_closed_rm_af_indexed_code}];
val inherited = map (fst o fst) (Thm_Deps.all_oracles [@{thm check_trs_termination_proof}]);
val used = map (fst o fst) (Thm_Deps.all_oracles audited);
val _ = if Thm_Deps.has_skip_proof audited orelse exists (fn n => not (member (op =) inherited n)) used then error "Untrusted indexed LP export" else ();
val (modules, _) = Code_Target.produce_code @{context} true [@{const_name check_lpc_return_nested_constructor_xml}, @{const_name check_lp_constructor_any_xml}, @{const_name check_lp_nontermination_all_xml},
   @{const_name check_lpc_xml}, @{const_name check_lpc_constructor_xml},
   @{const_name check_lpc_mgu_constructor_xml}, @{const_name lpc_xml_diagnostics},
   @{const_name check_lpc_return_composed_constructor_xml}, @{const_name check_lpc_return_composed_table_xml},
   @{const_name check_lpc_return_module_constructor_xml}, @{const_name check_lpc_return_constructor_xml},
   @{const_name check_lpc_return_module_table_xml}, @{const_name check_lpc_return_table_xml}] "Haskell" "LP_Return_Module_Generated" NONE [];
val root = Path.explode "/work/dfm/festschrift/CeTA-consolidated/target/usable-membership-20261026/lp-indexed/LP_Return_Module_Generated";
val _ = List.app (fn (names, bytes) => Bytes.write (root + Path.make names) bytes) modules;
val _ = writeln "EXPORTED_Indexed_LP_Return_Module_Generated";
\<close>
end
