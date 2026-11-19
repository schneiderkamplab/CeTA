theory Global_Boundary_Projection_Check
 imports Observer_Output_Rebase_Check
begin

text \<open>The global residual carries three value coordinates followed by
three structural coordinates. Both boundary clauses project the first two of
each. This proves their residual step, not the missing structural interpretation.\<close>

lemma global_equality_boundary_projection:
 assumes clause: "((source_symbol,map Var [x0,x1,x2,s0,s1,s2]),
   [(target_symbol,map Var [x0,x1,s0,s1])]) \<in> set Q"
 shows "([(source_symbol,map eta [x0,x1,x2,s0,s1,s2])],
   [(target_symbol,map eta [x0,x1,s0,s1])]) \<in> lp_ild Q"
 using lp_seg_residual_step[OF clause, where a="(source_symbol,map eta [x0,x1,x2,s0,s1,s2])"
   and \<sigma>=LPIVar and \<rho>=eta and rest="[]"]
 by (simp add: lp_atom_eval_def lp_iatom_subst_def o_def)

lemma global_equality_boundary_strict:
 assumes clause: "((source_symbol,map Var [x0,x1,x2,s0,s1,s2]),
   [(target_symbol,map Var [x0,x1,s0,s1])]) \<in> set Q"
 shows "([(source_symbol,map eta [x0,x1,x2,s0,s1,s2])],
   [(target_symbol,map eta [x0,x1,s0,s1])]) \<in> (lp_ild Q)\<^sup>+"
 using global_equality_boundary_projection[OF clause] by blast

lemma global_equality_boundary_preserves_observer:
 assumes represented: "lpc_reinterface (\<lambda>env x. env (Inl x)) runtime = lpc_return_eval eta
   [(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],
     [Fun f [Fun g [],Var ''V2''],Var ''V2'',Var ''V0''])]"
 and invariant: "lpp_observer_output_invariant A specs rest 2 hi runtime"
 and clause: "((source_symbol,map Var [''V0'',''V1'',''V2'',s0,s1,s2]),
   [(target_symbol,map Var [''V0'',''V1'',s0,s1])]) \<in> set Q"
 defines child_def: "child \<equiv> lpp_observer_rebase (\<lambda>_ _. lpc_return_env [Var ''V0'',Var ''V1''] eta) runtime"
 shows "lpc_reinterface (\<lambda>env x. env (Inl x)) child =
   lpc_return_eval eta [(LPCGoals [LPCUnify (Var ''V0'') (Var ''V1'')],[Var ''V0'',Var ''V1''])] \<and>
   lpp_observer_output_invariant A specs rest 0 hi child \<and>
   lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) child) =
   lpc_attach_answers rest (lpc_reinterface (\<lambda>env x. env (Inr x)) runtime) \<and>
   ([(source_symbol,map eta [''V0'',''V1'',''V2'',s0,s1,s2])],
    [(target_symbol,map eta [''V0'',''V1'',s0,s1])]) \<in> (lp_ild Q)\<^sup>+"
 unfolding child_def
 using arithmetic_equality_payload_rebase[OF represented invariant]
   global_equality_boundary_strict[OF clause, of eta] by blast

lemma wrong_structural_projection_detected:
 assumes different: "eta s0 \<noteq> eta s2"
 shows "map eta [x0,x1,s0,s1] \<noteq> map eta [x0,x1,s2,s1]"
 using different by simp

ML \<open>
val checked = @{thms global_equality_boundary_projection global_equality_boundary_strict
 wrong_structural_projection_detected global_equality_boundary_preserves_observer};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted global projection" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-boundary-projection/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Structural interpretation remains open.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_BOUNDARY_PROJECTION_KERNEL_CHECKED";
\<close>
end
