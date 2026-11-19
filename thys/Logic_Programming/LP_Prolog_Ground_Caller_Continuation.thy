theory LP_Prolog_Ground_Caller_Continuation
 imports LP_Prolog_Parameter_Head_Return
begin

text \<open>The continuation's caller output may become ground through sharing.
This local mode does not restrict arbitrary original-query outputs. Preservation
still requires authenticated bounded images on the actual caller support.\<close>

definition lpp_caller_output_mode where
 "lpp_caller_output_mode value = ((\<exists>x. value=LPIVar x) \<or> lp_seg_ground value)"

lemma lpp_caller_output_mode_substitute:
 fixes sigma :: "'v \<Rightarrow> ('f,'v) lp_iterm"
 assumes mode: "lpp_caller_output_mode value"
 and images: "lpp_bounded_images A sigma (set2_lp_iterm value)"
 and ground: "\<And>u. u\<in>A \<Longrightarrow> vars_term u={}"
 shows "lpp_caller_output_mode (lp_isubst value sigma)"
proof (cases "lp_seg_ground value")
 case True
 show ?thesis using True lp_seg_ground_subst[OF True, of sigma]
  by (simp add: lpp_caller_output_mode_def)
next
 case False
 obtain x where val_eq: "value=LPIVar x"
  using mode False by (auto simp: lpp_caller_output_mode_def)
 show ?thesis using images ground
  by (auto simp: val_eq lpp_caller_output_mode_def lpp_bounded_images_def lp_seg_ground_eval)
qed

lemma lpp_ground_caller_copy_resolution:
 assumes mgu: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 and parameter: "lp_seg_ground parameter"
 and ground_output: "lp_seg_ground output_value"
 shows "output_value= parameter \<and> rho n= parameter"
 using mgu parameter ground_output
 by (auto simp: lpc_mgu_resolve_def lp_seg_ground_subst)

lemma lpp_ground_caller_copy_mismatch:
 assumes parameter: "lp_seg_ground parameter"
 and ground_output: "lp_seg_ground output_value"
 and mismatch: "output_value\<noteq>parameter"
 shows "\<not>lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
proof
 assume resolved: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 show False using lpp_ground_caller_copy_resolution[OF resolved parameter ground_output] mismatch by simp
qed

lemma lpp_ground_caller_copy_matching:
 assumes spine: "lpp_finite_spine cons nil input_value spine_length"
 and mgu: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 and parameter: "lp_seg_ground parameter"
 and ground_output: "lp_seg_ground output_value"
 shows "lp_ieval (Fun p [Fun nil [],Var n,Var n]) (\<lambda>_. parameter) =
   LPIFun p [input_value,parameter,output_value]"
 using lpp_parameter_copy_head_input[OF spine mgu]
   lpp_ground_caller_copy_resolution[OF mgu parameter ground_output] by simp

lemma lpp_ground_caller_copy_leaf:
 assumes spine: "lpp_finite_spine cons nil input_value spine_length"
 and mgu: "lpc_mgu_resolve (LPIFun p [input_value,parameter,output_value]) gs
   (Fun p [Fun nil [],Var n,Var n]) bs sigma rho"
 and parameter: "lp_seg_ground parameter"
 and ground_output: "lp_seg_ground output_value"
 and finite_call: "lpp_finite_term (LPIFun p [input_value,parameter,output_value])"
 and finite_rest: "lpp_finite_goals gs"
 and covered: "set2_lp_iterm value \<subseteq> set2_lp_iterm (LPIFun p [input_value,parameter,output_value]) \<union>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). set2_lp_iterm t)"
 and known: "lpp_runtime_leaf_effect A observed value"
 and ground: "\<And>u. u\<in>A \<Longrightarrow> vars_term u={}"
 shows "lpp_runtime_leaf_effect A observed (lp_isubst value sigma)"
 by (rule lpp_runtime_leaf_effect_substitute[OF known
   lpp_runtime_matching_leaf_images[OF mgu lpp_ground_caller_copy_matching[OF spine mgu parameter ground_output]
    finite_call finite_rest covered] ground])

ML \<open>
val checked = @{thms lpp_caller_output_mode_substitute lpp_ground_caller_copy_resolution
 lpp_ground_caller_copy_mismatch lpp_ground_caller_copy_matching lpp_ground_caller_copy_leaf};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted ground caller continuation" else ();
\<close>
end
