theory Acquired_Resolution_Link_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Acquired_Univ_Resolution_Link"
begin

lemma old_namespace_positive:
 "lp_cut_resolution_env 3 6 eta sigma rho ''N''=eta ''N''"
 by (simp add: lp_cut_resolution_env_def)
lemma active_namespace_positive:
 "lp_cut_resolution_env 3 6 eta sigma rho ''$$$N''=lp_isubst (eta ''N'') sigma"
 by (simp add: lp_cut_resolution_env_def numeral_3_eq_3)
lemma clause_namespace_positive:
 "lp_cut_resolution_env 3 6 eta sigma rho ''$$$$$$N''=rho ''N''"
 by (simp add: lp_cut_resolution_env_def numeral_3_eq_3)
lemma stale_namespace_negative:
 "eta ''N''\<noteq>rho ''N'' \<Longrightarrow> lp_cut_resolution_env 3 6 eta sigma rho ''N''\<noteq>rho ''N''"
 by (simp add: lp_cut_resolution_env_def)
ML \<open>
val checked = @{thms lpp_acquired_univ_resolution_link old_namespace_positive active_namespace_positive clause_namespace_positive stale_namespace_negative};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted normalized acquisition" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-acquired-resolution-link/kernel-receipt.txt")
 ("Isabelle checked; no skipped proofs or oracles. Conditional normalized preservation; resolution link equations, knowledge, free choices and fork contexts derived for the supplied MGU; node assembly remains open.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "ACQUIRED_RESOLUTION_LINK_RECEIPT_CHECKED";
\<close>
end
