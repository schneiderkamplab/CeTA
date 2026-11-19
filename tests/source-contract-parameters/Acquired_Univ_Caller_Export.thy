theory Acquired_Univ_Caller_Export
 imports "../../thys/Logic_Programming/LP_Prolog_Acquired_Univ_Caller"
   "../../thys/Logic_Programming/LP_Prolog_Observer_Matching_Node"
   "../../thys/Logic_Programming/LP_Prolog_Separation_Subject_XML"
begin

definition test_clause_coordinate :: "nat \<Rightarrow> (string lp_cut_symbol,string) term \<Rightarrow>
 (string lp_cut_symbol,string) term \<Rightarrow> (string * (string lp_cut_symbol,string) term) list \<Rightarrow> bool" where
 "test_clause_coordinate = lpp_check_clause_coordinate"
definition test_body_output :: "(string lp_cut_symbol,string) term \<Rightarrow>
 (string lp_cut_symbol,string) term lp_cut_goal list \<Rightarrow> nat \<Rightarrow> string \<Rightarrow>
 (string lp_cut_symbol,string) term \<Rightarrow> (string * (string lp_cut_symbol,string) term) list \<Rightarrow> bool" where
 "test_body_output = lpp_check_body_output"

definition test_matching_outputs :: "string list \<Rightarrow> (string lp_cut_symbol,string) term \<Rightarrow>
 (string lp_cut_symbol,string) term lp_cut_goal list \<Rightarrow> (string lp_cut_symbol,string) term \<Rightarrow>
 (string * (string lp_cut_symbol,string) term) list \<Rightarrow> bool" where
 "test_matching_outputs = lpp_check_matching_outputs"
definition test_leaf_slots :: "nat list \<Rightarrow> (string lp_cut_symbol,nat) term lp_cut_goal list \<Rightarrow> bool" where
 "test_leaf_slots = lpp_check_attached_leaf_slots"

definition test_fresh_clause :: "(string lp_cut_symbol,string) term \<Rightarrow>
 (string lp_cut_symbol,string) term lp_cut_goal list \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> bool" where
 "test_fresh_clause = lpp_check_fresh_univ_clause"

ML \<open>
val checked = @{thms lpp_acquired_univ_caller_protection lpp_acquired_univ_caller_leaf_step};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted head successor gate" else ();
val output = Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-acquired-univ-caller";
val _ = File.write (output + Path.basic "kernel-receipt.txt")
 ("Isabelle checked; no skipped proofs or oracles. Full family and Split contracts remain open.\n" ^
  cat_lines (map (Thm.string_of_thm @{context}) checked));
val (modules, _) = Code_Target.produce_code @{context} true
 [@{const_name test_fresh_clause}, @{const_name test_matching_outputs}, @{const_name test_leaf_slots}, @{const_name test_clause_coordinate}, @{const_name test_body_output},
  @{const_name lpp_decode_separation_states}, @{const_name lpp_decode_separation_actions},
  @{const_name lpp_decode_separation_subject}, @{const_name lpp_check_functor_source_action},
  @{const_name lpcl_bindings}, @{const_name lpcl_target}]
 "SML" "Acquired_Univ_Caller_Check" NONE [];
val _ = if length modules=1 then () else error "Unexpected export module count";
val _ = Bytes.write (output + Path.basic "Acquired_Univ_Caller_Check.ML") (snd(hd modules));
val _ = writeln "ACQUIRED_UNIV_CALLER_CHECKED_AND_EXPORTED";
\<close>
end
