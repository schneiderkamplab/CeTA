theory LP_Prolog_Matching_Context_Structure
 imports LP_Prolog_Reflexive_Structure
begin

text \<open>Matching resolution preserves observed caller values, including
those carried only by the active continuation. Saved alternatives have their
own environments and are not included in the active substitution.\<close>

lemma lpp_matching_context_inverse:
 fixes eta sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve (lp_ieval call eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
 and matching: "lp_ieval h nu = lp_ieval call eta"
 shows "\<exists>delta. \<forall>x\<in>vars_term call \<union>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t).
   lp_isubst (lp_isubst (eta x) sigma) delta = eta x"
proof -
 have comparison: "lp_isubst (lp_ieval call eta) LPIVar = lp_ieval h nu"
  using matching by simp
 obtain delta where atom_factor:
   "lp_isubst (lp_isubst (lp_ieval call eta) sigma) delta = lp_ieval call eta"
  and goals_factor: "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta))
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) =
   map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs"
  using mgu comparison unfolding lpc_mgu_resolve_def by fastforce
 have atom_variables: "lp_isubst (lp_isubst (eta x) sigma) delta = eta x"
  if "x\<in>vars_term call" for x
  using lpc_ieval_variables_eq[OF _ that] atom_factor
  by (simp add: lp_ieval_subst)
 have goal_variables: "lp_isubst (lp_isubst (eta x) sigma) delta = eta x"
  if member: "g\<in>set gs" "t\<in>set (lp_cut_terms g)" "x\<in>vars_term t" for g t x
 proof -
  have mapped: "lp_cut_map (\<lambda>t. lp_isubst (lp_isubst (lp_ieval t eta) sigma) delta) g =
    lp_cut_map (\<lambda>t. lp_ieval t eta) g"
   using goals_factor member(1) by (simp add: map_map o_def lp_cut_map_comp map_eq_conv)
  have evaluated: "lp_isubst (lp_isubst (lp_ieval t eta) sigma) delta = lp_ieval t eta"
   using mapped member(2) by (cases g) auto
  show ?thesis using lpc_ieval_variables_eq[OF _ member(3)] evaluated
   by (simp add: lp_ieval_subst)
 qed
 show ?thesis by (rule exI[of _ delta]) (use atom_variables goal_variables in blast)
qed

lemma lpp_matching_context_structural_observation:
 fixes eta sigma rho :: "string \<Rightarrow> ('f,string) lp_iterm"
 assumes mgu: "lpc_mgu_resolve (lp_ieval call eta)
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs) h bs sigma rho"
 and matching: "lp_ieval h nu = lp_ieval call eta"
 and covered: "x\<in>vars_term call \<union>
   (\<Union>g\<in>set gs. \<Union>t\<in>set (lp_cut_terms g). vars_term t)"
 and finite: "lpp_finite_term (eta x)"
 shows "\<exists>observed_tree. lpp_runtime_structure (eta x) observed_tree \<and>
   lpp_runtime_structure (lp_isubst (eta x) sigma) observed_tree"
proof -
 obtain delta where inverse: "lp_isubst (lp_isubst (eta x) sigma) delta = eta x"
  using lpp_matching_context_inverse[OF mgu matching] covered by blast
 show ?thesis by (rule lpp_finite_inverse_structural_observation[OF finite inverse])
qed

ML \<open>
val checked = @{thms lpp_matching_context_inverse lpp_matching_context_structural_observation};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted matching context structure" else ();
\<close>
end
