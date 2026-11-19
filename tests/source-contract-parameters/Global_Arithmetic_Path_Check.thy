theory Global_Arithmetic_Path_Check
 imports Global_Boundary_Valuation_Check
begin

lemma boundary_projection_actual_values:
 assumes clause: "((boundary_symbol,map Var [v0,v1,v2,t0,t1,t2]),
   [(equality_symbol,map Var [v0,v1,t0,t1])]) \<in> set Q"
 and distinct: "distinct [v0,v1,v2,t0,t1,t2]"
 shows "([(boundary_symbol,[a0,a1,a2,b0,b1,b2])],[(equality_symbol,[a0,a1,b0,b1])]) \<in> lp_ild Q"
proof -
 let ?rho = "\<lambda>x. if x=v0 then a0 else if x=v1 then a1 else if x=v2 then a2
   else if x=t0 then b0 else if x=t1 then b1 else b2"
 show ?thesis using global_equality_boundary_projection[OF clause, of ?rho] distinct by auto
qed

lemma arithmetic_to_equality_observed_path:
 fixes eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
 and encode :: "(string lp_cut_symbol) lpp_structure_symbol \<Rightarrow> string lp_cut_symbol"
 assumes arithmetic: "((arithmetic_symbol,map Var [x,p,sx,sp]),
   [(boundary_symbol,map Var [x,z,p,sx,sz,sp])]) \<in> set Q"
 and projection: "((boundary_symbol,map Var [v0,v1,v2,t0,t1,t2]),
   [(equality_symbol,map Var [v0,v1,t0,t1])]) \<in> set Q"
 and distinct: "distinct [v0,v1,v2,t0,t1,t2]"
 and fresh: "z \<notin> {x,p,sx,sp}" "sz \<notin> {x,p,sx,sp}" "z \<noteq> sz"
 and observed: "observed_leaf_coordinate encode A initial_tree (eta x) (eta sx)"
 shows "\<exists>shadow.
   observed_leaf_coordinate encode A (Fun (Inl scalar) []) (LPIFun scalar [] :: (string lp_cut_symbol,string) lp_iterm) shadow \<and>
   ([(arithmetic_symbol,map eta [x,p,sx,sp])],
    [(equality_symbol,[eta x,LPIFun scalar [],eta sx,shadow])]) \<in> (lp_ild Q)\<^sup>+ \<and>
   observed_leaf_coordinate encode A initial_tree (eta x) (eta sx)"
proof -
 obtain shadow :: "(string lp_cut_symbol,string) lp_iterm" where scalar_observed:
  "observed_leaf_coordinate encode A (Fun (Inl scalar) []) (LPIFun scalar [] :: (string lp_cut_symbol,string) lp_iterm) shadow"
  using scalar_observation_exists[of encode A scalar] by blast
 let ?nu = "eta(z := LPIFun scalar [], sz := shadow)"
 have first: "([(arithmetic_symbol,map eta [x,p,sx,sp])],
   [(boundary_symbol,[eta x,LPIFun scalar [],eta p,eta sx,shadow,eta sp])]) \<in> lp_ild Q"
  using lp_seg_residual_step[OF arithmetic, where a="(arithmetic_symbol,map eta [x,p,sx,sp])"
    and \<sigma>=LPIVar and \<rho>="?nu" and rest="[]"] fresh
  by (auto simp: lp_atom_eval_def lp_iatom_subst_def o_def)
 have second: "([(boundary_symbol,[eta x,LPIFun scalar [],eta p,eta sx,shadow,eta sp])],
   [(equality_symbol,[eta x,LPIFun scalar [],eta sx,shadow])]) \<in> lp_ild Q"
  by (rule boundary_projection_actual_values[OF projection distinct])
 have path: "([(arithmetic_symbol,map eta [x,p,sx,sp])],
   [(equality_symbol,[eta x,LPIFun scalar [],eta sx,shadow])]) \<in> (lp_ild Q)\<^sup>+"
  using first second by (meson r_into_trancl trancl_trans)
 show ?thesis using scalar_observed observed path by blast
qed

lemma overwritten_output_observation_rejected:
 assumes different: "changed \<noteq> eta sx"
 shows "[eta x,LPIFun scalar [],changed,shadow] \<noteq> [eta x,LPIFun scalar [],eta sx,shadow]"
 using different by simp

ML \<open>
val checked = @{thms boundary_projection_actual_values arithmetic_to_equality_observed_path
 overwritten_output_observation_rejected};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted arithmetic global path" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-arithmetic-path/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Incoming output observation preserved, not reset.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_ARITHMETIC_PATH_KERNEL_CHECKED";
\<close>
end
