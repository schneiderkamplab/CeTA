theory LP_Prolog_Reflexive_Structure
 imports LP_Prolog_Structural_Projection LP_Prolog_Reflexive_Free
begin

lemma lpp_finite_inverse_structural_observation:
 assumes finite: "lpp_finite_term t"
 and inverse: "lp_isubst (lp_isubst t sigma) delta=t"
 shows "\<exists>observed_tree. lpp_runtime_structure t observed_tree \<and>
   lpp_runtime_structure (lp_isubst t sigma) observed_tree"
proof -
 obtain template where initial: "t=lp_ieval template LPIVar"
  using lpp_finite_runtime_template[OF finite] by blast
 have roundtrip: "lp_isubst (lp_ieval u sigma) delta=lp_ieval u LPIVar"
  if "u\<in>set [template]" for u
  using inverse initial that by (simp add: lp_ieval_subst)
 obtain rename where preserved: "lp_ieval template sigma=lp_ieval template (LPIVar \<circ> rename)"
  using lpc_finite_roundtrip_renaming[where ts="[template]", OF roundtrip] by auto
 have target: "lp_isubst t sigma=lp_ieval (map_term id rename template) LPIVar"
  by (simp add: initial lp_ieval_subst preserved lpp_ieval_template_rename)
 have old: "lpp_runtime_structure t (lpp_structure_template template)"
  unfolding lpp_runtime_structure_def using initial by blast
 have new: "lpp_runtime_structure (lp_isubst t sigma) (lpp_structure_template template)"
  unfolding lpp_runtime_structure_def
  by (rule exI[of _ "map_term id rename template"]) (simp add: target lpp_structure_template_rename)
 show ?thesis using old new by blast
qed

lemma lpp_reflexive_context_structural_observation:
 fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_unify (lp_ieval a eta) (lp_ieval b eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) sigma"
 and equal: "lp_ieval a eta=lp_ieval b eta"
 and occurs: "x\<in>(\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 and finite: "lpp_finite_term (eta x)"
 shows "\<exists>observed_tree. lpp_runtime_structure (eta x) observed_tree \<and>
   lpp_runtime_structure (lp_isubst (eta x) sigma) observed_tree"
proof -
 have comparison: "lp_isubst (lp_ieval a eta) LPIVar=lp_isubst (lp_ieval b eta) LPIVar"
  using equal by simp
 obtain delta where factor:
  "\<forall>g\<in>set gs. \<forall>t\<in>set (lp_cut_terms g). \<forall>v\<in>vars_term t.
   lp_isubst (lp_isubst (eta v) sigma) delta=eta v"
  using lpc_mgu_unify_context_factor[OF mgu comparison] by auto
 have inverse: "lp_isubst (lp_isubst (eta x) sigma) delta=eta x"
  using factor occurs by blast
 show ?thesis by (rule lpp_finite_inverse_structural_observation[OF finite inverse])
qed

ML \<open>
val checked = @{thms lpp_finite_inverse_structural_observation lpp_reflexive_context_structural_observation};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted reflexive structural transport" else ();
\<close>
end
