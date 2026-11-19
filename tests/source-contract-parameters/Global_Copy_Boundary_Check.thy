theory Global_Copy_Boundary_Check
 imports Copy_Empty_Interface_Check
begin

lemma copy_zero_interface_return_path:
 fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes boundary: "((source_symbol,map Var xs),[(cut_symbol,[])]) \<in> set Q"
 and cut: "((cut_symbol,[]),[(success_symbol,[])]) \<in> set Q"
 and returned: "((success_symbol,[]),[(return_symbol,[])]) \<in> set Q"
 shows "([(source_symbol,map eta xs)],[(return_symbol,[])]) \<in> (lp_ild Q)\<^sup>+"
proof -
 have first: "([(source_symbol,map eta xs)],[(cut_symbol,[])]) \<in> lp_ild Q"
  using lp_seg_residual_step[OF boundary, where a="(source_symbol,map eta xs)"
   and \<sigma>=LPIVar and \<rho>=eta and rest="[]"]
  by (simp add: lp_atom_eval_def lp_iatom_subst_def o_def)
 have second: "([(cut_symbol,[] :: (string lp_cut_symbol,string) lp_iterm list)],[(success_symbol,[])]) \<in> lp_ild Q"
  using lp_seg_residual_step[OF cut, where a="(cut_symbol,[])"
   and \<sigma>=LPIVar and \<rho>=eta and rest="[]"]
  by (simp add: lp_atom_eval_def lp_iatom_subst_def)
 have third: "([(success_symbol,[] :: (string lp_cut_symbol,string) lp_iterm list)],[(return_symbol,[])]) \<in> lp_ild Q"
  using lp_seg_residual_step[OF returned, where a="(success_symbol,[])"
   and \<sigma>=LPIVar and \<rho>=eta and rest="[]"]
  by (simp add: lp_atom_eval_def lp_iatom_subst_def)
 show ?thesis using first second third by (meson r_into_trancl trancl_trans)
qed

lemma tracked_copy_zero_interface_contract:
 fixes env :: "nat+nat \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 assumes invariant: "lpp_observer_output_invariant A specs rest oi hi [(LPCGoals [LPCCut m],env)]"
 and helper_value: "env (Inl oi) = parameter"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and boundary: "((source_symbol,map Var xs),[(cut_symbol,[])]) \<in> set Q"
 and cut: "((cut_symbol,[]),[(success_symbol,[])]) \<in> set Q"
 and return_clause: "((success_symbol,[]),[(return_symbol,[])]) \<in> set Q"
 and continuation: "\<And>rho. rho hi = parameter \<Longrightarrow>
   lpp_runtime_parameter initial_parameter (rho hi) \<Longrightarrow>
   list_all (\<lambda>(slot,tree). lpp_runtime_leaf_effect A tree (rho slot)) specs \<Longrightarrow>
   lpp_finite_execution [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
    [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] (lp_ild Q) [(return_symbol,[])] returned"
 shows "lp_answer_contract (lpp_domain_answers P B U D)
  (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x)) [(LPCGoals [LPCCut m],env)]))
  (lp_ild Q) [(source_symbol,map eta xs)] returned"
proof -
 have path: "([(source_symbol,map eta xs)],[(return_symbol,[])]) \<in> (lp_ild Q)\<^sup>+"
  by (rule copy_zero_interface_return_path[OF boundary cut return_clause])
 have lower: "lp_answer_contract (lpp_domain_answers P B U D)
  (lpc_attach_answers rest (lpc_reinterface (\<lambda>e x. e (Inr x)) [(LPCGoals [LPCCut m],env)]))
  (lp_ild Q) [(return_symbol,[])] returned"
  by (rule tracked_copy_cut_return[OF invariant helper_value tracked continuation])
 show ?thesis by (rule lp_answer_contract_start[OF trancl_into_rtrancl[OF path] lower])
qed

ML \<open>
val checked = @{thms copy_zero_interface_return_path tracked_copy_zero_interface_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted copy boundary" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-copy-empty-interface/boundary-kernel-receipt.txt")
 ("Kernel checked; no skips or oracles. Caller contract and family assembly remain explicit.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_COPY_BOUNDARY_KERNEL_CHECKED";
\<close>
end
