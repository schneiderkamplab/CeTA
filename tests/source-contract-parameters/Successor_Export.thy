theory Successor_Export
 imports "../../thys/Logic_Programming/LP_Prolog_Head_Successor_Facts"
   "../../thys/Logic_Programming/LP_Prolog_Separation_Subject_XML"
begin

definition test_clause_coordinate :: "nat \<Rightarrow> (string lp_cut_symbol,string) term \<Rightarrow>
 (string lp_cut_symbol,string) term \<Rightarrow> (string * (string lp_cut_symbol,string) term) list \<Rightarrow> bool" where
 "test_clause_coordinate = lpp_check_clause_coordinate"
definition test_body_output :: "(string lp_cut_symbol,string) term \<Rightarrow>
 (string lp_cut_symbol,string) term lp_cut_goal list \<Rightarrow> nat \<Rightarrow> string \<Rightarrow>
 (string lp_cut_symbol,string) term \<Rightarrow> (string * (string lp_cut_symbol,string) term) list \<Rightarrow> bool" where
 "test_body_output = lpp_check_body_output"

ML \<open>
val checked = @{thms lpp_checked_clause_coordinate_value lpp_checked_head_coordinate_value
 lpp_checked_head_parameter_successor lpp_checked_head_free_successor lpp_checked_body_output_free
 lpp_checked_body_output_separate_head lpp_checked_body_output_separate_caller
 lpp_checked_recursive_head_successor_facts lpp_checked_matching_head_successor_facts
 lpp_clause_coordinate_positive lpp_clause_coordinate_stale_negative lpp_body_output_head_variable_rejected
 lpp_body_output_positive lpp_body_output_missing_occurrence_negative};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted head successor gate" else ();
val output = Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-head-successors";
val _ = File.write (output + Path.basic "kernel-receipt.txt")
 ("Isabelle checked; no skipped proofs or oracles. Full family and Split contracts remain open.\n" ^
  cat_lines (map (Thm.string_of_thm @{context}) checked));
val (modules, _) = Code_Target.produce_code @{context} true
 [@{const_name test_clause_coordinate}, @{const_name test_body_output},
  @{const_name lpp_decode_separation_states}, @{const_name lpp_decode_separation_actions},
  @{const_name lpp_decode_separation_subject}, @{const_name lpp_check_functor_source_action},
  @{const_name lpcl_bindings}, @{const_name lpcl_target}]
 "SML" "Successor_Check" NONE [];
val _ = if length modules=1 then () else error "Unexpected export module count";
val _ = Bytes.write (output + Path.basic "Successor_Check.ML") (snd(hd modules));
val _ = writeln "HEAD_SUCCESSOR_RULES_CHECKED_AND_EXPORTED";
\<close>
end
