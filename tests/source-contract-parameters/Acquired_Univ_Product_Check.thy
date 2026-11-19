theory Acquired_Univ_Product_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Acquired_Univ_Product"
begin

lemma acquired_caller_projection:
 "lpc_reinterface (\<lambda>env slot. env (Inr slot))
   ((frame,case_sum helper (\<lambda>slot. lp_isubst (caller slot) sigma))#saved) =
   (frame,\<lambda>slot. lp_isubst (caller slot) sigma)#
   lpc_reinterface (\<lambda>env slot. env (Inr slot)) saved"
 by (simp add: lpc_reinterface_def)

lemma acquired_helper_projection:
 "lpc_reinterface (\<lambda>env slot. env (Inl slot))
   ((frame,case_sum helper caller)#saved) =
   (frame,helper)#lpc_reinterface (\<lambda>env slot. env (Inl slot)) saved"
 by (simp add: lpc_reinterface_def)

ML \<open>
val checked = @{thms lpp_acquired_normalized_univ_product acquired_caller_projection
 acquired_helper_projection lpp_observer_invariant_missing_saved_finite};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted acquired product" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-acquired-univ-product/kernel-receipt.txt")
 ("Isabelle checked; no skipped proofs or oracles. Joint caller entry derived from acquisition; helper representation and coverage remain premises.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "ACQUIRED_UNIV_PRODUCT_RECEIPT_CHECKED";
\<close>
end
