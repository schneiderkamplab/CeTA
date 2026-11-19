theory LP_Prolog_Ground_Output_Images
 imports LP_Prolog_Parameter_Subterms LP_Prolog_Ground_Caller_Continuation
begin

lemma lpp_ground_instance_variable_subterm:
 fixes sigma :: "'v \<Rightarrow> ('f,'v) lp_iterm"
 assumes equation: "lp_isubst (lp_ieval t LPIVar) sigma=lp_ieval c LPIVar"
 and ground: "vars_term c={}"
 and occurrence: "x\<in>vars_term t"
 shows "\<exists>u. lpp_finite_template_subterm u c \<and> sigma x=lp_ieval u LPIVar"
 using equation ground occurrence
proof (induct t arbitrary: c)
 case (Var y)
 show ?case using Var by (auto intro: lpp_finite_template_subterm.root)
next
 case (Fun f ts)
 obtain g cs where target: "c=Fun g cs"
  using Fun.prems(2) by (cases c) auto
 have maps: "map (\<lambda>t. lp_isubst (lp_ieval t LPIVar) sigma) ts=map (\<lambda>t. lp_ieval t LPIVar) cs"
  using Fun.prems(1) by (simp add: target map_map o_def)
 have lengths: "length ts=length cs" using arg_cong[OF maps, of length] by simp
 obtain i where index: "i<length ts" and occurs: "x\<in>vars_term (ts!i)"
  using Fun.prems(3) by (auto simp: in_set_conv_nth)
 have child_eq: "lp_isubst (lp_ieval (ts!i) LPIVar) sigma=lp_ieval (cs!i) LPIVar"
  using arg_cong[OF maps, of "\<lambda>xs. xs!i"] index lengths by simp
 have child_ground: "vars_term (cs!i)={}"
  using Fun.prems(2) index lengths by (auto simp: target)
 obtain u where sub: "lpp_finite_template_subterm u (cs!i)" and image: "sigma x=lp_ieval u LPIVar"
  using Fun.hyps[OF nth_mem[OF index] child_eq child_ground occurs] by blast
 have parent: "lpp_finite_template_subterm u c"
  unfolding target by (rule lpp_finite_template_subterm.child[OF nth_mem sub]) (use index lengths in simp)
 show ?case using parent image by blast
qed

lemma lpp_ground_runtime_output_images:
 fixes sigma :: "'v \<Rightarrow> ('f,'v) lp_iterm"
 assumes finite: "lpp_finite_term output_value"
 and equation: "lp_isubst output_value sigma=lp_ieval c LPIVar"
 and ground: "vars_term c={}"
 shows "lpp_bounded_images (lpp_parameter_subterm_templates f g c) sigma (set2_lp_iterm output_value)"
proof -
 obtain t where represented: "output_value=lp_ieval t LPIVar"
  using lpp_finite_runtime_template[OF finite] by blast
 have member: "c\<in>lpp_parameter_leaf_templates f g c"
  by (simp add: lpp_parameter_leaf_templates_def)
 have images: "\<exists>u\<in>lpp_parameter_subterm_templates f g c. sigma x=lp_ieval u LPIVar"
  if "x\<in>vars_term t" for x
  using lpp_ground_instance_variable_subterm[OF equation[unfolded represented] ground that] member
  by (auto simp: lpp_parameter_subterm_templates_def)
 show ?thesis using images by (simp add: represented lpp_template_runtime_support lpp_bounded_images_def)
qed

lemma lpp_partial_caller_copy_output_images:
 assumes actual: "lpc_mgu_resolve (LPIFun p [input_value,lp_ieval c LPIVar,output_value]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 and ground: "vars_term c={}"
 and finite: "lpp_finite_term output_value"
 shows "lpp_bounded_images (lpp_parameter_subterm_templates f g c) sigma (set2_lp_iterm output_value)"
proof -
 have parameter_ground: "lp_seg_ground (lp_ieval c LPIVar)"
  using ground by (simp add: lp_seg_ground_eval)
 have eq: "lp_isubst (LPIFun p [input_value,lp_ieval c LPIVar,output_value]) sigma=
   lp_ieval (Fun p [Fun nil [],Var n,Var n]) rho"
  using actual by (simp only: lpc_mgu_resolve_def)
 have copied: "lp_isubst output_value sigma=lp_ieval c LPIVar"
  using eq lp_seg_ground_subst[OF parameter_ground, of sigma] by auto
 show ?thesis by (rule lpp_ground_runtime_output_images[OF finite copied ground])
qed

lemma lpp_partial_caller_copy_shared_leaf:
 assumes actual: "lpc_mgu_resolve (LPIFun p [input_value,lp_ieval c LPIVar,output_value]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 and ground: "vars_term c={}"
 and finite: "lpp_finite_term output_value"
 and known: "lpp_runtime_leaf_effect (lpp_parameter_subterm_templates f g c) shape caller_value"
 and shared: "set2_lp_iterm caller_value \<subseteq> set2_lp_iterm output_value"
 shows "lpp_runtime_leaf_effect (lpp_parameter_subterm_templates f g c) shape (lp_isubst caller_value sigma)"
proof -
 have images: "lpp_bounded_images (lpp_parameter_subterm_templates f g c) sigma (set2_lp_iterm caller_value)"
  using lpp_partial_caller_copy_output_images[where f=f and g=g, OF actual ground finite] shared
  unfolding lpp_bounded_images_def by blast
 show ?thesis by (rule lpp_runtime_leaf_effect_substitute[OF known images])
   (rule lpp_parameter_subterm_templates_ground[OF ground])
qed

ML \<open>
val checked = @{thms lpp_ground_instance_variable_subterm lpp_ground_runtime_output_images lpp_partial_caller_copy_output_images lpp_partial_caller_copy_shared_leaf};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted ground output images" else ();
val _ = writeln "GROUND_OUTPUT_IMAGES_KERNEL_CHECKED";
\<close>
end
