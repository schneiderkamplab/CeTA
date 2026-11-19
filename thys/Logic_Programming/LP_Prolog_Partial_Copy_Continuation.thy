theory LP_Prolog_Partial_Copy_Continuation
 imports LP_Prolog_Ground_Output_Images LP_Cut_Joint_Free LP_Prolog_Runtime_Ground_Head_Leaf
begin

lemma lpp_partial_copy_continuation_images:
 fixes sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes actual: "lpc_mgu_resolve (lp_ieval (Fun p [Fun nil [],c,t]) LPIVar)
   (map (lp_cut_map (\<lambda>u. lp_ieval u LPIVar)) gs)
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 and ground: "vars_term c={}"
 shows "lpp_bounded_images (lpp_parameter_subterm_templates f g c) sigma
   (\<Union>goal\<in>set gs. \<Union>u\<in>set (lp_cut_terms goal). vars_term u)"
proof -
 let ?tau = "\<lambda>x. if x\<in>vars_term t then sigma x else LPIVar x"
 let ?nu = "\<lambda>_::string. lp_ieval c LPIVar"
 have parameter_ground: "lp_seg_ground (lp_ieval c LPIVar)"
  using ground by (simp add: lp_seg_ground_eval)
 have eq: "lp_isubst (lp_ieval (Fun p [Fun nil [],c,t]) LPIVar) sigma=
   lp_ieval (Fun p [Fun nil [],Var n,Var n]) rho"
  using actual by (simp only: lpc_mgu_resolve_def)
 have copied: "lp_isubst (lp_ieval t LPIVar) sigma=lp_ieval c LPIVar"
  using eq lp_seg_ground_subst[OF parameter_ground, of sigma] by auto
 have same_output: "lp_isubst (lp_ieval t LPIVar) ?tau=lp_isubst (lp_ieval t LPIVar) sigma"
  unfolding lp_ieval_subst by (rule lp_ieval_cong) auto
 have comparison: "lp_isubst (lp_ieval (Fun p [Fun nil [],c,t]) LPIVar) ?tau=
   lp_ieval (Fun p [Fun nil [],Var n,Var n]) ?nu"
  using copied same_output lp_seg_ground_subst[OF parameter_ground, of ?tau] by simp
 obtain delta where factor: "\<forall>x\<in>(\<Union>goal\<in>set gs. \<Union>u\<in>set (lp_cut_terms goal). vars_term u).
   lp_isubst (sigma x) delta=?tau x"
  using lpc_joint_mgu_factor[OF actual comparison] by auto
 have bounded: "(\<exists>y. sigma x=LPIVar y) \<or>
   (\<exists>u\<in>lpp_parameter_subterm_templates f g c. sigma x=lp_ieval u LPIVar)"
  if live: "x\<in>(\<Union>goal\<in>set gs. \<Union>u\<in>set (lp_cut_terms goal). vars_term u)" for x
 proof (cases "x\<in>vars_term t")
  case True
  obtain u where sub: "lpp_finite_template_subterm u c" and image: "sigma x=lp_ieval u LPIVar"
   using lpp_ground_instance_variable_subterm[OF copied ground True] by blast
  have member: "u\<in>lpp_parameter_subterm_templates f g c"
   using sub by (auto simp: lpp_parameter_subterm_templates_def lpp_parameter_leaf_templates_def)
  show ?thesis using member image by blast
 next
  case False
  have inverse: "lp_isubst (sigma x) delta=LPIVar x" using factor[rule_format, OF live] False by simp
  have variable: "\<exists>y. sigma x=LPIVar y" using inverse by (cases "sigma x") auto
  show ?thesis using variable by blast
 qed
 show ?thesis using bounded by (simp add: lpp_bounded_images_def)
qed

lemma lpp_partial_copy_runtime_continuation_images:
 assumes actual: "lpc_mgu_resolve (LPIFun p [input_value,lp_ieval c LPIVar,output_value]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and ground: "vars_term c={}"
 and finite_output: "lpp_finite_term output_value"
 and finite_rest: "lpp_finite_goals gs"
 shows "lpp_bounded_images (lpp_parameter_subterm_templates f g c) sigma
   (\<Union>goal\<in>set gs. \<Union>u\<in>set (lp_cut_terms goal). set2_lp_iterm u)"
proof -
 have empty_input: "input_value=LPIFun nil []"
  by (rule lpp_parameter_copy_head_input[OF spine actual])
 obtain t where output_template: "output_value=lp_ieval t LPIVar"
  using lpp_finite_runtime_template[OF finite_output] by blast
 obtain qs where goals: "map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) qs=gs"
  using lpp_finite_goal_templates[OF finite_rest] by blast
 have represented: "lpc_mgu_resolve (lp_ieval (Fun p [Fun nil [],c,t]) LPIVar)
   (map (lp_cut_map (\<lambda>u. lp_ieval u LPIVar)) qs)
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
  using actual by (simp add: empty_input output_template goals)
 show ?thesis
  using lpp_partial_copy_continuation_images[where f=f and g=g, OF represented ground]
  unfolding goals[symmetric] lpp_evaluated_goals_runtime_support .
qed

lemma lpp_partial_copy_caller_leaf:
 assumes actual: "lpc_mgu_resolve (LPIFun p [input_value,lp_ieval c LPIVar,output_value]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and ground: "vars_term c={}"
 and finite_output: "lpp_finite_term output_value"
 and finite_rest: "lpp_finite_goals gs"
 and known: "lpp_runtime_leaf_effect (lpp_parameter_subterm_templates f g c) shape caller_value"
 and covered: "set2_lp_iterm caller_value \<subseteq>
   (\<Union>goal\<in>set gs. \<Union>u\<in>set (lp_cut_terms goal). set2_lp_iterm u)"
 shows "lpp_runtime_leaf_effect (lpp_parameter_subterm_templates f g c) shape (lp_isubst caller_value sigma)"
proof -
 have images: "lpp_bounded_images (lpp_parameter_subterm_templates f g c) sigma (set2_lp_iterm caller_value)"
  using lpp_partial_copy_runtime_continuation_images[where f=f and g=g,
    OF actual spine ground finite_output finite_rest] covered
  unfolding lpp_bounded_images_def by (meson subsetD)
 show ?thesis by (rule lpp_runtime_leaf_effect_substitute[OF known images])
  (rule lpp_parameter_subterm_templates_ground[OF ground])
qed

lemma lpp_partial_copy_tracked_caller_leaf:
 assumes actual: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 and spine: "lpp_finite_spine cons nil input_value spine_length"
 and tracked: "lpp_runtime_parameter initial_parameter parameter"
 and finite_output: "lpp_finite_term output_value"
 and finite_rest: "lpp_finite_goals gs"
 and known: "lpp_runtime_leaf_effect (lpp_parameter_subterm_templates f g initial_parameter) shape caller_value"
 and covered: "set2_lp_iterm caller_value \<subseteq>
   (\<Union>goal\<in>set gs. \<Union>u\<in>set (lp_cut_terms goal). set2_lp_iterm u)"
 shows "lpp_runtime_leaf_effect (lpp_parameter_subterm_templates f g initial_parameter) shape (lp_isubst caller_value sigma)"
proof -
 obtain d where initial_ground: "vars_term initial_parameter={}"
 and returned: "lpp_parameter_return initial_parameter d" and parameter: "parameter=lp_ieval d LPIVar"
  using tracked by (auto simp: lpp_runtime_parameter_def)
 have ground: "vars_term d={}" by (rule lpp_parameter_return_ground[OF initial_ground returned])
 have all_images: "lpp_bounded_images (lpp_parameter_subterm_templates f g d) sigma
   (\<Union>goal\<in>set gs. \<Union>u\<in>set (lp_cut_terms goal). set2_lp_iterm u)"
  by (rule lpp_partial_copy_runtime_continuation_images[OF actual[unfolded parameter] spine ground finite_output finite_rest])
 have included: "lpp_parameter_subterm_templates f g d \<subseteq> lpp_parameter_subterm_templates f g initial_parameter"
  by (rule lpp_parameter_return_subterm_templates[OF returned])
 have images: "lpp_bounded_images (lpp_parameter_subterm_templates f g initial_parameter) sigma (set2_lp_iterm caller_value)"
  using all_images covered included unfolding lpp_bounded_images_def by (meson subsetD)
 show ?thesis by (rule lpp_runtime_leaf_effect_substitute[OF known images])
  (rule lpp_parameter_subterm_templates_ground[OF initial_ground])
qed

ML \<open>
val checked = @{thms lpp_partial_copy_continuation_images lpp_partial_copy_runtime_continuation_images lpp_partial_copy_caller_leaf lpp_partial_copy_tracked_caller_leaf};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted partial copy continuation" else ();
val _ = writeln "PARTIAL_COPY_CONTINUATION_KERNEL_CHECKED";
\<close>
end
