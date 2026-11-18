theory LP_Prolog_Ground_Head_Leaf
 imports LP_Prolog_Leaf_Spine_Head LP_Prolog_Finite_Anchored_Head
begin

text \<open>The leaf-count/size order permits arbitrary finite ground
replacements. Groundness alone is insufficient: a ground rational term can
still have infinite structure. The finite instantiated-head premise is kept.\<close>

lemma lpp_finite_evaluation_images:
 assumes finite: "lpp_finite_term (lp_ieval t sigma)"
 and member: "x\<in>vars_term t"
 shows "lpp_finite_term (sigma x)"
 using finite member by (induct t) (auto simp: list_all_iff)

lemma lpp_resolution_extends_bounded_call_images:
 fixes sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve (lp_ieval call LPIVar)
   (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) h bs sigma rho"
 and selected: "lpp_bounded_images A sigma (vars_term call)"
 and covered: "V\<subseteq>vars_term call \<union>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_bounded_images A sigma V"
proof -
 let ?comparison = "\<lambda>x. if x\<in>vars_term call then sigma x else LPIVar x"
 have same: "lp_ieval call ?comparison=lp_ieval call sigma"
  by (rule lp_ieval_cong) simp
 have comparison: "lp_isubst (lp_ieval call LPIVar) ?comparison=lp_ieval h rho"
  using same mgu by (simp add: lpc_mgu_resolve_def lp_ieval_subst)
 obtain delta where factor:
  "\<forall>g\<in>set gs. \<forall>t\<in>set (lp_cut_terms g). \<forall>x\<in>vars_term t.
    lp_isubst (sigma x) delta=?comparison x"
  using lpc_mgu_context_factor[OF mgu comparison] by auto
 show ?thesis
 proof (unfold lpp_bounded_images_def, intro ballI)
  fix x assume member: "x\<in>V"
  show "(\<exists>y. sigma x=LPIVar y) \<or> (\<exists>u\<in>A. sigma x=lp_ieval u LPIVar)"
  proof (cases "x\<in>vars_term call")
   case True
   then show ?thesis using selected by (auto simp: lpp_bounded_images_def)
  next
   case False
   have occurs: "x\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
    using member covered False by blast
   have inverse: "lp_isubst (sigma x) delta=LPIVar x"
    using factor occurs False by auto
   show ?thesis using lpc_isubst_variable_reflect[OF inverse] by blast
  qed
 qed
qed

lemma lpp_ground_instance_resolution_leaf_images:
 fixes sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve (lp_ieval call LPIVar)
   (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) h bs sigma rho"
 and finite: "lpp_finite_term (lp_ieval h rho)"
 and ground: "lp_seg_ground (lp_ieval h rho)"
 and covered: "V\<subseteq>vars_term call \<union>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_bounded_images {u. vars_term u={}} sigma V"
proof -
 have equation: "lp_ieval call sigma=lp_ieval h rho"
  using mgu by (simp add: lpc_mgu_resolve_def lp_ieval_subst)
 have selected: "lpp_bounded_images {u. vars_term u={}} sigma (vars_term call)"
 proof (unfold lpp_bounded_images_def, intro ballI)
  fix x assume member: "x\<in>vars_term call"
  have finite_x: "lpp_finite_term (sigma x)"
   by (rule lpp_finite_evaluation_images[OF _ member]) (use finite equation in simp)
  have ground_call: "lp_seg_ground (lp_ieval call sigma)"
   using ground by (simp only: equation)
  have ground_x: "lp_seg_ground (sigma x)"
   using ground_call member by (auto simp: lp_seg_ground_eval)
  obtain u where represented: "sigma x=lp_ieval u LPIVar"
   using lpp_finite_runtime_template[OF finite_x] by blast
  have "vars_term u={}"
   using ground_x by (auto simp: represented lp_seg_ground_eval elim: lp_seg_ground.cases)
  then show "(\<exists>y. sigma x=LPIVar y) \<or>
    (\<exists>u\<in>{u. vars_term u={}}. sigma x=lp_ieval u LPIVar)"
   using represented by blast
 qed
 show ?thesis by (rule lpp_resolution_extends_bounded_call_images[OF mgu selected covered])
qed

lemma lpp_ground_instance_preserves_caller_leaf:
 fixes sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve (lp_ieval call LPIVar)
   (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) h bs sigma rho"
 and finite: "lpp_finite_term (lp_ieval h rho)"
 and ground: "lp_seg_ground (lp_ieval h rho)"
 and known: "lpp_runtime_leaf_effect {u. vars_term u={}} initial_structure runtime_value"
 and covered: "set2_lp_iterm runtime_value\<subseteq>vars_term call \<union>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_runtime_leaf_effect {u. vars_term u={}} initial_structure (lp_isubst runtime_value sigma)"
 by (rule lpp_runtime_leaf_effect_substitute[OF known
   lpp_ground_instance_resolution_leaf_images[OF mgu finite ground covered]]) simp

ML \<open>
val checked = @{thms lpp_finite_evaluation_images lpp_resolution_extends_bounded_call_images
 lpp_ground_instance_resolution_leaf_images lpp_ground_instance_preserves_caller_leaf};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted ground head leaf transport" else ();
\<close>
end
