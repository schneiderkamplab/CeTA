theory Observer_Output_Alias_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Observer_Output_Alias"
begin

lemma same_output_positive:
 "lpp_observer_output_alias (2::nat) (0::nat)
  [((),case_sum (\<lambda>i. if i = 2 then LPIVar (''h''::string) else LPIVar ''x'')
    (\<lambda>_. LPIVar ''h''))]"
 by (simp add: lpp_observer_output_alias_def)

lemma wrong_output_negative:
 "\<not> lpp_observer_output_alias (1::nat) (0::nat)
  [((),case_sum (\<lambda>i. if i = 2 then LPIVar (''h''::string) else LPIVar ''x'')
    (\<lambda>_. LPIVar ''h''))]"
 by (simp add: lpp_observer_output_alias_def)

lemma stale_saved_output_negative:
 "\<not> lpp_observer_output_alias (2::nat) (0::nat)
  [((),\<lambda>_. LPIVar (''h''::string)),
   ((),case_sum (\<lambda>_. LPIVar ''x'') (\<lambda>_. LPIVar ''h''))]"
 by (simp add: lpp_observer_output_alias_def)

ML \<open>
val checked = @{thms lpp_observer_output_alias_step lpp_observer_output_alias_initial
 lpp_observer_output_alias_projection lpp_observer_output_alias_scopes
 lpp_observer_output_alias_mode same_output_positive wrong_output_negative stale_saved_output_negative};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted output alias fixture" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-observer-output-alias/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "OBSERVER_OUTPUT_ALIAS_KERNEL_CHECKED";
\<close>
end
