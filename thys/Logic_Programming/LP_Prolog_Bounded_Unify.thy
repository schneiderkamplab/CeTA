theory LP_Prolog_Bounded_Unify
 imports LP_Prolog_Bounded_Instantiation LP_Cut_MGU_Unify_Free
begin

text \<open>A most-general source equality may instantiate its selected free
variable to an allowed ground template. Other observed variables remain free,
provided they occur in the actual continuation. No assumption is imposed on
fresh locals which are absent from that observed support.\<close>

lemma lpp_ground_binding_bounded_images:
 fixes sigma :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_unify (LPIVar x) (lp_ieval u LPIVar)
   (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) sigma"
 and ground_template: "vars_term u={}"
 and allowed: "u\<in>A"
 and covered: "V\<subseteq>insert x (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 shows "lpp_bounded_images A sigma V"
proof -
 have ground_value: "lp_seg_ground (lp_ieval u LPIVar)"
  using ground_template by (simp add: lp_seg_ground_eval)
 let ?comparison = "LPIVar(x:=lp_ieval u LPIVar)"
 have comparison: "lp_isubst (lp_ieval (Var x) LPIVar) ?comparison =
   lp_isubst (lp_ieval u LPIVar) ?comparison"
  by (simp add: lp_seg_ground_subst[OF ground_value])
 have typed_mgu: "lpc_mgu_unify (lp_ieval (Var x) LPIVar) (lp_ieval u LPIVar)
   (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) sigma"
  using mgu by simp
 obtain delta where factor:
  "\<forall>g\<in>set gs. \<forall>t\<in>set (lp_cut_terms g). \<forall>v\<in>vars_term t.
   lp_isubst (sigma v) delta=?comparison v"
  using lpc_mgu_unify_context_factor[OF typed_mgu comparison] by auto
 have bound: "sigma x=lp_ieval u LPIVar"
  using mgu by (simp add: lpc_mgu_unify_def lp_seg_ground_subst[OF ground_value])
 show ?thesis
 proof (unfold lpp_bounded_images_def, intro ballI)
  fix v assume member: "v\<in>V"
  show "(\<exists>y. sigma v=LPIVar y) \<or> (\<exists>t\<in>A. sigma v=lp_ieval t LPIVar)"
  proof (cases "v=x")
   case True
   then show ?thesis using bound allowed by blast
  next
   case False
   have occurs: "v\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
    using member covered False by blast
   have inverse: "lp_isubst (sigma v) delta=LPIVar v"
    using factor occurs False by auto
   show ?thesis using lpc_isubst_variable_reflect[OF inverse] by blast
  qed
 qed
qed


lemma lpp_ground_binding_structural_effect:
 fixes sigma :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_unify (LPIVar x) (lp_ieval u LPIVar)
   (map (lp_cut_map (\<lambda>t. lp_ieval t LPIVar)) gs) sigma"
 and ground_template: "vars_term u={}"
 and allowed: "u\<in>A"
 and covered: "vars_term t\<subseteq>insert x (\<Union>g\<in>set gs. \<Union>q\<in>set (lp_cut_terms g). vars_term q)"
 shows "\<exists>v. lp_isubst (lp_ieval t LPIVar) sigma=lp_ieval v LPIVar \<and>
  lpp_leaf_effect A (lpp_structure_template t) (lpp_structure_template v)"
 by (rule lpp_bounded_runtime_structural_effect)
   (rule lpp_ground_binding_bounded_images[OF mgu ground_template allowed covered])

lemma lpp_unobserved_binding_not_bounded:
 fixes x y :: string and f g :: 'f
 assumes distinct: "x\<noteq>y" "f\<noteq>g"
 defines "sigma \<equiv> LPIVar(x:=LPIFun f [],y:=LPIFun g [])"
 shows "lpc_mgu_unify (LPIVar x) (LPIFun f []) [] sigma \<and>
   \<not>lpp_bounded_images {Fun f []} sigma {y}"
 using distinct unfolding sigma_def lpc_mgu_unify_def lpp_bounded_images_def
 by auto

ML \<open>
val checked = @{thms lpp_ground_binding_bounded_images lpp_ground_binding_structural_effect
 lpp_unobserved_binding_not_bounded};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted bounded source equality" else ();
\<close>
end
