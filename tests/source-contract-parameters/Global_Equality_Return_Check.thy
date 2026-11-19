theory Global_Equality_Return_Check
 imports Global_Arithmetic_Path_Check Equality_Output_Preservation_Check
begin

lemma observed_coordinate_new_leaf_history:
 assumes effect: "lpp_runtime_leaf_effect A initial_tree runtime_value"
 and observed: "observed_leaf_coordinate encode B previous_tree runtime_value shadow"
 shows "observed_leaf_coordinate encode A initial_tree runtime_value shadow"
 using effect observed lpp_runtime_structure_unique
 unfolding lpp_runtime_leaf_effect_def observed_leaf_coordinate_def by blast

lemma scalar_equality_reuses_observation:
 fixes a :: "(string lp_cut_symbol,string) lp_iterm"
 assumes actual: "lpc_mgu_unify a (LPIFun (LPCUser scalar) []) gs sigma"
 and finite_rest: "lpp_finite_goals gs"
 and effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) initial_tree a"
 and ground: "vars_term initial_parameter = {}"
 and observed: "observed_leaf_coordinate encode B scalar_tree
   (LPIFun (LPCUser scalar) [] :: (string lp_cut_symbol,string) lp_iterm) shadow"
 shows "lp_isubst a sigma = LPIFun (LPCUser scalar) [] \<and>
   observed_leaf_coordinate encode (lpp_parameter_leaf_templates f g initial_parameter)
    initial_tree (lp_isubst a sigma) shadow"
proof -
 let ?A = "lpp_parameter_leaf_templates f g initial_parameter"
 have finite_call: "lpp_finite_term a" using lpp_runtime_leaf_effect_finite[OF effect] .
 have allowed: "Fun (LPCUser scalar) [] \<in> ?A" by (simp add: lpp_parameter_leaf_templates_def)
 have each_ground: "vars_term v = {}" if "v \<in> ?A" for v
  by (rule lpp_parameter_leaf_templates_ground[OF ground that])
 have closed: "v \<in> ?A" if "lpp_finite_template_subterm v (Fun (LPCUser scalar) [])" for v
  using that allowed by (cases rule: lpp_finite_template_subterm.cases) auto
 have mgu: "lpc_mgu_unify a (lp_ieval (Fun (LPCUser scalar) []) LPIVar) gs sigma"
  using actual by simp
 have images: "lpp_bounded_images ?A sigma (set2_lp_iterm a)"
  by (rule lpp_subterm_ground_equality_images[OF mgu finite_call finite_rest _ allowed closed]) auto
 have after_effect: "lpp_runtime_leaf_effect ?A initial_tree (lp_isubst a sigma)"
  by (rule lpp_runtime_leaf_effect_substitute[OF effect images each_ground])
 have result_value: "lp_isubst a sigma = LPIFun (LPCUser scalar) []"
  using actual by (simp add: lpc_mgu_unify_def)
 show ?thesis using observed_coordinate_new_leaf_history[OF after_effect] observed result_value by simp
qed

lemma equality_global_return_path:
 assumes success_clause: "((eq_symbol,map Var [x0,x1,s0,s1]),[(success_symbol,map Var [x1,s1])]) \<in> set Q"
 and return_clause: "((success_symbol,map Var [y,t]),[(return_symbol,map Var [y,y,t,t])]) \<in> set Q"
 and distinct: "distinct [x0,x1,s0,s1]" "y \<noteq> t"
 shows "([(eq_symbol,[a,scalar,old_shadow,scalar_shadow])],
   [(return_symbol,[scalar,scalar,scalar_shadow,scalar_shadow])]) \<in> (lp_ild Q)\<^sup>+"
proof -
 let ?rho = "\<lambda>x. if x=x0 then a else if x=x1 then scalar else if x=s0 then old_shadow else scalar_shadow"
 have first: "([(eq_symbol,[a,scalar,old_shadow,scalar_shadow])],[(success_symbol,[scalar,scalar_shadow])]) \<in> lp_ild Q"
  using lp_seg_residual_step[OF success_clause, where a="(eq_symbol,[a,scalar,old_shadow,scalar_shadow])"
   and \<sigma>=LPIVar and \<rho>="?rho" and rest="[]"] distinct
  by (auto simp: lp_atom_eval_def lp_iatom_subst_def o_def)
 let ?nu = "\<lambda>x. if x=y then scalar else scalar_shadow"
 have second: "([(success_symbol,[scalar,scalar_shadow])],[(return_symbol,[scalar,scalar,scalar_shadow,scalar_shadow])]) \<in> lp_ild Q"
  using lp_seg_residual_step[OF return_clause, where a="(success_symbol,[scalar,scalar_shadow])"
   and \<sigma>=LPIVar and \<rho>="?nu" and rest="[]"] distinct
  by (auto simp: lp_atom_eval_def lp_iatom_subst_def o_def)
 show ?thesis using first second by (meson r_into_trancl trancl_trans)
qed

lemma actual_scalar_equality_global_return:
 fixes a :: "(string lp_cut_symbol,string) lp_iterm"
 assumes actual: "lpc_mgu_unify a (LPIFun (LPCUser scalar) []) gs sigma"
 and finite_rest: "lpp_finite_goals gs"
 and effect: "lpp_runtime_leaf_effect (lpp_parameter_leaf_templates f g initial_parameter) initial_tree a"
 and ground: "vars_term initial_parameter = {}"
 and observed: "observed_leaf_coordinate encode B scalar_tree
   (LPIFun (LPCUser scalar) [] :: (string lp_cut_symbol,string) lp_iterm) shadow"
 and success_clause: "((eq_symbol,map Var [x0,x1,s0,s1]),[(success_symbol,map Var [x1,s1])]) \<in> set Q"
 and return_clause: "((success_symbol,map Var [y,t]),[(return_symbol,map Var [y,y,t,t])]) \<in> set Q"
 and distinct: "distinct [x0,x1,s0,s1]" "y \<noteq> t"
 shows "observed_leaf_coordinate encode (lpp_parameter_leaf_templates f g initial_parameter)
   initial_tree (lp_isubst a sigma) shadow \<and>
   ([(eq_symbol,[a,LPIFun (LPCUser scalar) [],old_shadow,shadow])],
    [(return_symbol,[lp_isubst a sigma,lp_isubst a sigma,shadow,shadow])]) \<in> (lp_ild Q)\<^sup>+"
 using scalar_equality_reuses_observation[OF actual finite_rest effect ground observed]
 by (metis equality_global_return_path[OF success_clause return_clause distinct])

ML \<open>
val checked = @{thms observed_coordinate_new_leaf_history scalar_equality_reuses_observation equality_global_return_path actual_scalar_equality_global_return};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted equality return coordinates" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-global-equality-return/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Full helper return and caller continuation remain open.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "GLOBAL_EQUALITY_RETURN_KERNEL_CHECKED";
\<close>
end
