theory Acquired_Block_Rows_Export
 imports "../../thys/Logic_Programming/LP_Prolog_Acquired_Univ_Entry"
 "../../thys/Logic_Programming/LP_Prolog_Observer_Internal_Coverage"
 "../../thys/Logic_Programming/LP_Prolog_Separation_Subject_XML"
begin
ML \<open>
val checked = @{thms lpp_checked_observer_equality_row lpp_checked_observer_univ_row
 lpp_acquired_univ_normalized_from_resolution};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted acquired block rows" else ();
val output = Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-acquired-block-rows";
val _ = File.write (output + Path.basic "kernel-receipt.txt")
 ("Checked theorem dependencies; no skipped proofs or oracles. Runtime row audit is separate; full block assembly remains open.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
val (modules, _) = Code_Target.produce_code @{context} true
 [@{const_name lpp_decode_separation_states}, @{const_name lpp_decode_separation_actions},
 @{const_name lpp_decode_separation_subject}, @{const_name lpp_decode_separation_witnesses},
 @{const_name lpp_check_observer_equality_row}, @{const_name lpp_check_observer_univ_row}]
 "SML" "Acquired_Block_Rows_Check" NONE [];
val _ = if length modules=1 then () else error "Unexpected export module count";
val _ = Bytes.write (output + Path.basic "Acquired_Block_Rows_Check.ML") (snd(hd modules));
val _ = writeln "ACQUIRED_BLOCK_ROWS_CHECKED_AND_EXPORTED";
\<close>
end
