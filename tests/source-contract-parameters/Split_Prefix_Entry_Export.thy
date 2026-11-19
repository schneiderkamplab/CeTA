theory Split_Prefix_Entry_Export
 imports "../../thys/Logic_Programming/LP_Prolog_Split_Prefix_Caller_Entry"
begin

definition test_prefix_slots :: "(string lp_cut_symbol,string) term list \<Rightarrow>
 string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
 "test_prefix_slots = lpp_check_prefix_caller_coordinates"

ML \<open>
val checked = @{thms lpp_prefix_caller_coordinate_values lpp_split_prefix_caller_initial};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted split prefix entry export" else ();
val output = Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-split-prefix-entry";
val _ = File.write (output + Path.basic "kernel-receipt.txt")
 ("Isabelle checked; no skipped proofs or oracles. Initial caller invariant only; preservation and returns remain open.\n" ^
  cat_lines (map (Thm.string_of_thm @{context}) checked));
val (modules, _) = Code_Target.produce_code @{context} true
 [@{const_name test_prefix_slots}] "SML" "Split_Prefix_Entry_Check" NONE [];
val _ = if length modules=1 then () else error "Unexpected export module count";
val _ = Bytes.write (output + Path.basic "Split_Prefix_Entry_Check.ML") (snd(hd modules));
val _ = writeln "SPLIT_PREFIX_ENTRY_CHECKED_AND_EXPORTED";
\<close>
end
