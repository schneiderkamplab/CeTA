theory Normalized_Univ_Product_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Normalized_Univ_Product"
begin

lemma continuing_pair_positive:
 "lpp_observer_continuing_equality_frame [(LPCGoals [LPCUnify a b,LPCAtom c],env)]"
 by simp

lemma missing_tail_negative:
 "\<not>lpp_observer_continuing_equality_frame [(LPCGoals [LPCUnify a b],env)]"
 by simp

lemma aliased_outputs_negative:
 "\<not>lpc_free_knowledge {''name'',''args''}
   (\<lambda>_. LPIVar (''shared''::string) :: (string lp_cut_symbol,string) lp_iterm)"
 by (simp add: lpc_free_knowledge_def inj_on_def)

ML \<open>
val checked = @{thms lpp_normalized_univ_observer_product continuing_pair_positive
 missing_tail_negative aliased_outputs_negative};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted normalized product check" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-normalized-univ-product/kernel-receipt.txt")
 ("Isabelle checked; no skipped proofs or oracles. Conditional synchronized product; acquisition assembly and returns remain open.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "NORMALIZED_UNIV_PRODUCT_RECEIPT_CHECKED";
\<close>
end
