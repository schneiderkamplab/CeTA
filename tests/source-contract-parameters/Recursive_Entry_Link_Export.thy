theory Recursive_Entry_Link_Export
 imports "../../thys/Logic_Programming/LP_Prolog_Recursive_Entry_Link"
begin

definition test_entry_transport :: "string list \<Rightarrow> string list \<Rightarrow>
 (string * (string lp_cut_symbol,string) term) list \<Rightarrow> bool" where
 "test_entry_transport source_slots target_slots bindings =
 (case (source_slots,target_slots) of ([i,p,h,t,c],[i',p',h',t',c']) \<Rightarrow>
  lpp_check_recursive_entry_transport i p h t c i' p' h' t' c'
    (lp_cut_instance_subst bindings) | _ \<Rightarrow> False)"

ML \<open>
val checked = @{thms lpp_checked_recursive_entry_transport lpp_stable_functor_link_with_recursive_entry};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted recursive entry link export" else ();
val output = Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-recursive-entry-link";
val _ = File.write (output + Path.basic "kernel-receipt.txt")
 ("Isabelle checked; no skipped proofs or oracles. Boundary link premises and Splits remain open.\n" ^
  cat_lines (map (Thm.string_of_thm @{context}) checked));
val (modules, _) = Code_Target.produce_code @{context} true
 [@{const_name test_entry_transport}] "SML" "Recursive_Entry_Link_Check" NONE [];
val _ = if length modules=1 then () else error "Unexpected export module count";
val _ = Bytes.write (output + Path.basic "Recursive_Entry_Link_Check.ML") (snd(hd modules));
val _ = writeln "RECURSIVE_ENTRY_LINK_CHECKED_AND_EXPORTED";
\<close>
end
