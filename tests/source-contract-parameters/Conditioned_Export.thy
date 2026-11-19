theory Conditioned_Export
 imports "../../thys/Logic_Programming/LP_Prolog_Parameter_Equality_Node"
   "../../thys/Logic_Programming/LP_Prolog_Parameter_Refresh"
   "../../thys/Logic_Programming/LP_Prolog_Separation_Subject_XML"
begin

definition test_parameter_refresh :: "nat \<Rightarrow> nat \<Rightarrow> string list \<Rightarrow>
 (string lp_cut_symbol,string) term \<Rightarrow> (string lp_cut_symbol,string) term \<Rightarrow>
 (string * (string lp_cut_symbol,string) term) list \<Rightarrow> bool" where
 "test_parameter_refresh = lpp_check_parameter_refresh"

ML \<open>
val checked = @{thms lpp_conditioned_functor_link_sound
 lpp_conditioned_functor_equality_node_sound lpp_checked_observer_conditioned_equality_contract
 lpp_checked_observer_conditioned_parameter_equality_contract lpp_observer_parameter_equality_node_contract
 lpp_checked_parameter_refresh lpp_parameter_refresh_context_only lpp_parameter_refresh_raw_ground
 lpp_parameter_refresh_context_is_not_raw lpp_parameter_refresh_bad_bounds lpp_parameter_refresh_wrong_coordinate};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted conditioned equality gate" else ();
val output = Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-conditioned-equality";
val _ = File.write (output + Path.basic "kernel-receipt.txt")
 ("Isabelle checked; no skipped proofs or oracles. Complete Split contracts remain open.\n" ^
  cat_lines (map (Thm.string_of_thm @{context}) checked));
val (modules, _) = Code_Target.produce_code @{context} true
 [@{const_name test_parameter_refresh}, @{const_name lpp_decode_separation_states},
  @{const_name lpp_decode_separation_actions}, @{const_name lpp_decode_separation_subject},
  @{const_name lpp_check_functor_source_action}, @{const_name lpcn_ground},
  @{const_name lpcl_bindings}, @{const_name lpcl_target}]
 "SML" "Conditioned_Check" NONE [];
val _ = if length modules=1 then () else error "Unexpected export module count";
val _ = Bytes.write (output + Path.basic "Conditioned_Check.ML") (snd(hd modules));
val _ = writeln "CONDITIONED_PARAMETER_EQUALITY_CHECKED_AND_EXPORTED";
\<close>
end
