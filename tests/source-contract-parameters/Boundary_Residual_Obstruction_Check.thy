theory Boundary_Residual_Obstruction_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Observer_Conditioned_Output_Link"
begin

lemma absent_head_rejects_table_link:
 assumes absent: "\<forall>clause\<in>set Q. fst (fst clause) \<noteq> lpcn_pred nd"
 shows "\<not> lpc_check_link fuel Q nds nd s G K eqs e"
 using absent by (auto simp: lpc_check_link_def Let_def)

lemma absent_head_no_residual_step:
 assumes absent: "\<forall>clause\<in>set Q. fst (fst clause) \<noteq> symbol"
 shows "([ (symbol,actuals) ],u) \<notin> lp_ild Q"
 using absent
 by (auto elim!: lp_ild.cases simp: lp_iatom_subst_def lp_atom_eval_def split: prod.splits)

lemma absent_head_no_strict_residual_descent:
 assumes absent: "\<forall>clause\<in>set Q. fst (fst clause) \<noteq> symbol"
 shows "([(symbol,actuals)],u) \<notin> (lp_ild Q)\<^sup>+"
 using absent_head_no_residual_step[OF absent]
 by (auto simp: trancl_unfold_left)

ML \<open>
val checked = @{thms absent_head_rejects_table_link absent_head_no_residual_step absent_head_no_strict_residual_descent};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted boundary obstruction" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-boundary-residual-obstruction/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "BOUNDARY_RESIDUAL_OBSTRUCTION_KERNEL_CHECKED";
\<close>
end
