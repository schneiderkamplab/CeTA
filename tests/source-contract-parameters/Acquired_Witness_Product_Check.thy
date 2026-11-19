theory Acquired_Witness_Product_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Acquired_Univ_Witness_Product"
begin

lemma matching_helper_payload_positive:
 "lpc_reinterface (\<lambda>env slot. env (Inl slot))
   [(frame,case_sum helper caller)] = [(frame,helper)]"
 by (simp add: lpc_reinterface_def)

lemma omitted_saved_frame_negative:
 "lpc_reinterface (\<lambda>env slot. env (Inl slot))
   [(frame,case_sum helper caller),(old_frame,old_env)] \<noteq> [(frame,helper)]"
 by (simp add: lpc_reinterface_def)

lemma stale_helper_payload_negative:
 assumes "helper slot\<noteq>stale slot"
 shows "lpc_reinterface (\<lambda>env slot. env (Inl slot))
   [(frame,case_sum helper caller)] \<noteq> [(frame,stale)]"
 using assms by (auto simp: lpc_reinterface_def fun_eq_iff)

ML \<open>
val checked = @{thms lpp_acquired_univ_witness_product matching_helper_payload_positive
 omitted_saved_frame_negative stale_helper_payload_negative};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted acquired witness product" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-acquired-witness-product/kernel-receipt.txt")
 ("Isabelle checked; no skipped proofs or oracles. Helper representation derived conditionally; coordinate/payload/saved correspondence and coverage remain explicit.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "ACQUIRED_WITNESS_PRODUCT_RECEIPT_CHECKED";
\<close>
end
