theory Head_Export
 imports "../../thys/Logic_Programming/LP_Prolog_Parameter_Head_Return"
   "../../thys/Logic_Programming/LP_Prolog_Separation_Subject_XML"
begin

definition test_copy_head :: "(string lp_cut_symbol,string) term \<Rightarrow> bool" where
 "test_copy_head = lpp_check_parameter_copy_head"
definition test_matching_outputs :: "string list \<Rightarrow> (string lp_cut_symbol,string) term \<Rightarrow>
 (string lp_cut_symbol,string) term lp_cut_goal list \<Rightarrow> (string lp_cut_symbol,string) term \<Rightarrow>
 (string * (string lp_cut_symbol,string) term) list \<Rightarrow> bool" where
 "test_matching_outputs = lpp_check_matching_outputs"

ML \<open>
val checked = @{thms lpp_matching_free_outputs lpp_checked_matching_parameter_outputs
 lpp_parameter_copy_head_shape lpp_parameter_copy_head_input lpp_parameter_copy_head_return
 lpp_parameter_copy_head_caller_leaf lpp_parameter_copy_head_base_step
 lpp_matching_outputs_positive lpp_matching_outputs_missing_coverage_negative
 lpp_parameter_copy_head_positive lpp_parameter_copy_head_nonrepeated_negative};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted parameter head gate" else ();
val output = Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-parameter-heads";
val _ = File.write (output + Path.basic "kernel-receipt.txt")
 ("Isabelle checked; no skipped proofs or oracles. Full family and Split contracts remain open.\n" ^
  cat_lines (map (Thm.string_of_thm @{context}) checked));
val (modules, _) = Code_Target.produce_code @{context} true
 [@{const_name test_copy_head}, @{const_name test_matching_outputs},
  @{const_name lpp_decode_separation_states}, @{const_name lpp_decode_separation_actions},
  @{const_name lpp_decode_separation_subject}, @{const_name lpp_check_functor_source_action}]
 "SML" "Head_Check" NONE [];
val _ = if length modules=1 then () else error "Unexpected export module count";
val _ = Bytes.write (output + Path.basic "Head_Check.ML") (snd(hd modules));
val _ = writeln "PARAMETER_HEAD_RULES_CHECKED_AND_EXPORTED";
\<close>
end
