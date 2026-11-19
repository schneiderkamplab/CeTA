theory Partial_Equality_Successor_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Partial_Equality_Successor_Node"
begin
lemma equality_return_refresh_positive:
 "lpp_check_parameter_refresh 3 6 [''V1''] (Var ''V1'' :: (nat,string) term)
   (Var ''V0'') [(''V0'',Var ''V1'')]"
 by (simp add: lpp_check_parameter_refresh_def lp_cut_instance_subst_def lp_cut_refresh_def)
lemma equality_return_refresh_missing_negative:
 "\<not>lpp_check_parameter_refresh 3 6 [''V1''] (Var ''V1'' :: (nat,string) term)
   (Var ''V0'') []"
 by (simp add: lpp_check_parameter_refresh_def lp_cut_instance_subst_def lp_cut_refresh_def)
ML \<open>
val checked = @{thms lpp_partial_equality_successor_values lpp_observer_partial_equality_successor_node_contract equality_return_refresh_positive equality_return_refresh_missing_negative};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted recursive partial entry" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-partial-equality-successor/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Arbitrary finite caller output; no helper return or family discharge.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
\<close>
end
