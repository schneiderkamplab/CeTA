theory Recursive_Caller_Export
 imports "../../thys/Logic_Programming/LP_Prolog_Observer_Recursive_Caller_Node"
   "../../thys/Logic_Programming/LP_Prolog_Separation_Subject_XML"
begin

definition test_entry_coordinates :: "(string lp_cut_symbol,string) term \<Rightarrow>
 (string lp_cut_symbol,string) term lp_cut_goal list \<Rightarrow> nat \<Rightarrow>
 string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string \<Rightarrow>
 string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string \<Rightarrow>
 (string * (string lp_cut_symbol,string) term) list \<Rightarrow> bool" where
 "test_entry_coordinates = lpp_check_recursive_entry_coordinates"

definition shared_entry_fixture :: "string \<Rightarrow> nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm" where
 "shared_entry_fixture helper = (\<lambda>slot.
   if slot=1 then LPIFun (LPCUser ''seed'') []
   else if slot=2 then LPIVar helper
   else if slot=3 then lpp_argument_list [LPIVar ''caller'']
   else LPIVar ''caller'')"

lemma recursive_entry_shared_caller_positive:
 "lpp_recursive_caller_entry (Fun (LPCUser ''seed'') []) 0 1 2 3 4 (shared_entry_fixture ''helper'')"
proof -
 have tracked: "lpp_runtime_parameter (Fun (LPCUser ''seed'') []) (LPIFun (LPCUser ''seed'') [])"
  using lpp_runtime_parameter_initial[of "Fun (LPCUser ''seed'') []"] by simp
 show ?thesis using tracked lpp_argument_list_length[of "[LPIVar ''caller'']"]
  by (auto simp: lpp_recursive_caller_entry_def lpp_caller_output_mode_def shared_entry_fixture_def)
qed

lemma recursive_entry_aliased_outputs_negative:
 "\<not>lpp_recursive_caller_entry c 0 1 2 3 4 (shared_entry_fixture ''caller'')"
 by (simp add: lpp_recursive_caller_entry_def lpp_caller_output_mode_def shared_entry_fixture_def)

lemma recursive_entry_helper_in_input_negative:
 "\<not>lpp_recursive_caller_entry c 0 1 2 3 4
   ((shared_entry_fixture ''helper'')(0:=LPIVar ''helper''))"
 by (simp add: lpp_recursive_caller_entry_def lpp_caller_output_mode_def shared_entry_fixture_def)

lemma recursive_caller_ground_positive:
 "lpp_recursive_caller_entry (Fun (LPCUser ''seed'') []) 0 1 2 3 4
  ((shared_entry_fixture ''helper'')(4 := LPIFun (LPCUser ''bound'') [LPIFun (LPCUser ''atom'') []]))"
 using recursive_entry_shared_caller_positive
 by (simp add: lpp_recursive_caller_entry_def lpp_caller_output_mode_def shared_entry_fixture_def)

lemma recursive_caller_nonground_negative:
 "\<not>lpp_recursive_caller_entry c 0 1 2 3 4
  ((shared_entry_fixture ''helper'')(4 := LPIFun (LPCUser ''compound'') [LPIVar ''caller'']))"
 by (auto simp: lpp_recursive_caller_entry_def lpp_caller_output_mode_def shared_entry_fixture_def
   elim: lp_seg_ground.cases)

ML \<open>
val checked = @{thms lpp_checked_recursive_caller_entry recursive_entry_shared_caller_positive
 recursive_entry_aliased_outputs_negative recursive_entry_helper_in_input_negative
 recursive_caller_ground_positive recursive_caller_nonground_negative lpp_observer_recursive_caller_node_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted head successor gate" else ();
val output = Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-recursive-caller";
val _ = File.write (output + Path.basic "kernel-receipt.txt")
 ("Isabelle checked; no skipped proofs or oracles. Full family and Split contracts remain open.\n" ^
  cat_lines (map (Thm.string_of_thm @{context}) checked));
val (modules, _) = Code_Target.produce_code @{context} true
 [@{const_name test_entry_coordinates},
  @{const_name lpp_decode_separation_states}, @{const_name lpp_decode_separation_actions},
  @{const_name lpp_decode_separation_subject}, @{const_name lpp_check_functor_source_action},
  @{const_name lpcl_bindings}, @{const_name lpcl_target}]
 "SML" "Recursive_Caller_Check" NONE [];
val _ = if length modules=1 then () else error "Unexpected export module count";
val _ = Bytes.write (output + Path.basic "Recursive_Caller_Check.ML") (snd(hd modules));
val _ = writeln "RECURSIVE_CALLER_CHECKED_AND_EXPORTED";
\<close>
end
