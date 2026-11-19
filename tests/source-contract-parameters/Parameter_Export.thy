theory Parameter_Export
 imports "../../thys/Logic_Programming/LP_Prolog_Observer_Runtime_Parameter_Equality"
   "../../thys/Logic_Programming/LP_Prolog_Parameter_Coordinate_Link"
   "../../thys/Logic_Programming/LP_Prolog_Separation_Subject_XML"
begin

definition test_parameter_entry :: "string list \<Rightarrow> string lpp_source_context \<Rightarrow>
 (string lp_cut_symbol,string) term \<Rightarrow> bool" where
 "test_parameter_entry = lpp_check_parameter_entry"

definition test_parameter_coordinate :: "(string lp_cut_symbol,string) term \<Rightarrow>
 (string lp_cut_symbol,string) term \<Rightarrow>
 (string * (string lp_cut_symbol,string) term) list \<Rightarrow> bool" where
 "test_parameter_coordinate a b bindings =
  lpp_check_parameter_coordinate a b (lp_cut_instance_subst bindings)"

definition test_parameter_binding :: "string list \<Rightarrow> string \<Rightarrow>
 string lp_cut_symbol \<Rightarrow> string lp_cut_symbol \<Rightarrow>
 (string lp_cut_symbol,string) term \<Rightarrow> (string lp_cut_symbol,string) term \<Rightarrow> bool" where
 "test_parameter_binding = lpp_check_parameter_binding"

ML \<open>
val checked = @{thms lpp_checked_parameter_entry lpp_runtime_parameter_compose
 lpp_runtime_parameter_subst lpp_runtime_parameter_scalar
 lpp_checked_parameter_coordinate_value lpp_checked_parameter_coordinate
 lpp_checked_parameter_coordinate_after_substitution
 lpp_actual_var_branch lpp_actual_var_success_free lpp_parameter_cut_keeps_active_facts
 lpp_opaque_var_guard_does_not_establish_free
 lpp_checked_observer_runtime_parameter_equality_contract
 lpp_checked_parameter_branch_coordinates lpp_stable_functor_link_with_parameter_facts};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted source parameter rules" else ();
val output = Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-contract-development";
val _ = File.write (output + Path.basic "kernel-receipt.txt")
 ("Isabelle checked; no skipped proofs or oracles. Source contracts remain open.\n" ^
  cat_lines (map (Thm.string_of_thm @{context}) checked));
val (modules, _) = Code_Target.produce_code @{context} true
 [@{const_name test_parameter_entry}, @{const_name test_parameter_coordinate},
  @{const_name test_parameter_binding}, @{const_name lpp_decode_separation_states},
  @{const_name lpp_decode_separation_links}, @{const_name lpcn_ground},
  @{const_name lpcl_bindings}, @{const_name lpcl_target}]
 "SML" "Parameter_Check" NONE [];
val _ = if length modules=1 then () else error "Unexpected export module count";
val _ = Bytes.write (output + Path.basic "Parameter_Check.ML") (snd(hd modules));
val _ = writeln "SOURCE_PARAMETER_RULES_CHECKED_AND_EXPORTED";
\<close>
end
