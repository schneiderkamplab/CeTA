theory LP_Cut_Domain_NO_Renaming
  imports LP_Cut_Domain_NO_Source
begin

context cut_runtime_domain
begin
lemma runtime_mgu_output_swap:
  fixes a :: "unit \<times> ('f lp_cut_symbol,string) lp_iterm list"
  assumes mgu: "lp_runtime_mgu D a b sigma"
  shows "lp_runtime_mgu D a b
    (\<lambda>v. lp_isubst (sigma v) (\<lambda>w. LPIVar (lpc_no_swap x y w)))"
proof -
  let ?r = "\<lambda>w. LPIVar (lpc_no_swap x y w)"
  let ?s = "\<lambda>v. lp_isubst (sigma v) ?r"
  have ds: "\<forall>v. D (?s v)"
    using mgu unfolding lp_runtime_mgu_def by (auto intro: substitute variables)
  have original: "lp_iatom_subst a sigma = lp_iatom_subst b sigma"
    using mgu by (simp add: lp_runtime_mgu_def)
  have mapped: "lp_iatom_subst (lp_iatom_subst a sigma) ?r =
      lp_iatom_subst (lp_iatom_subst b sigma) ?r"
    by (rule arg_cong[OF original])
  have eq: "lp_iatom_subst a ?s = lp_iatom_subst b ?s"
    using mapped by (simp add: lp_iatom_subst_def map_map o_def lpc_isubst_comp)
  have factor: "\<exists>v. (\<forall>x. D (v x)) \<and> (\<forall>x. u x = lp_isubst (?s x) v)"
    if du: "\<forall>x. D (u x)" and eq: "lp_iatom_subst a u = lp_iatom_subst b u"
    for u :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
  proof -
    obtain v where dv: "\<forall>x. D (v x)"
      and fac: "\<forall>x. u x = lp_isubst (sigma x) v"
      using mgu du eq unfolding lp_runtime_mgu_def by blast
    show ?thesis
      by (intro exI[of _ "\<lambda>w. v (lpc_no_swap x y w)"])
        (simp add: dv fac lpc_isubst_comp)
  qed
  show ?thesis unfolding lp_runtime_mgu_def using ds eq factor by blast
qed

lemma fresh_resolution_output_swap:
  fixes a :: "('f lp_cut_symbol,string) lp_iterm"
  assumes "lp_fresh_resolution D a gs h bs sigma rho"
  shows "lp_fresh_resolution D a gs h bs
    (\<lambda>v. lp_isubst (sigma v) (\<lambda>w. LPIVar (lpc_no_swap x y w)))
    (\<lambda>v. lp_isubst (rho v) (\<lambda>w. LPIVar (lpc_no_swap x y w)))"
  using assms unfolding lp_fresh_resolution_def
  by (auto simp: o_def intro: runtime_mgu_output_swap)

lemma mgu_resolve_output_swap:
  fixes a :: "('f lp_cut_symbol,string) lp_iterm"
  assumes mgu: "mgu_resolve a gs h bs sigma rho"
  shows "mgu_resolve a gs h bs
    (\<lambda>v. lp_isubst (sigma v) (\<lambda>w. LPIVar (lpc_no_swap x y w)))
    (\<lambda>v. lp_isubst (rho v) (\<lambda>w. LPIVar (lpc_no_swap x y w)))"
proof -
  let ?r = "\<lambda>w. LPIVar (lpc_no_swap x y w)"
  let ?s = "\<lambda>v. lp_isubst (sigma v) ?r"
  let ?rho = "\<lambda>v. lp_isubst (rho v) ?r"
  have unifies: "lp_isubst a ?s = lp_ieval h ?rho"
    using arg_cong[OF conjunct1[OF mgu[unfolded mgu_resolve_def]],
      of "\<lambda>t. lp_isubst t (\<lambda>w. LPIVar (lpc_no_swap x y w))"]
    by (simp add: lpc_isubst_comp lp_ieval_subst)
  have factor: "\<forall>(tau :: string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm) nu. (\<forall>x. D (tau x)) \<longrightarrow> (\<forall>x. D (nu x)) \<longrightarrow> lp_isubst a tau = lp_ieval h nu \<longrightarrow>
    (\<exists>delta. (\<forall>x. D (delta x)) \<and> lp_isubst (lp_isubst a ?s) delta = lp_isubst a tau \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t ?s) delta)) gs =
      map (lp_cut_map (\<lambda>t. lp_isubst t tau)) gs \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t ?rho) delta)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t nu)) bs)"
  proof (intro allI impI)
    fix tau nu :: "string \<Rightarrow> ('f lp_cut_symbol,string) lp_iterm"
    assume dt: "\<forall>x. D (tau x)" and dn: "\<forall>x. D (nu x)"
    assume "lp_isubst a tau = lp_ieval h nu"
    then obtain delta where dd: "\<forall>x. D (delta x)" and factor:
      "lp_isubst (lp_isubst a sigma) delta = lp_isubst a tau"
      "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta)) gs = map (lp_cut_map (\<lambda>t. lp_isubst t tau)) gs"
      "map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t rho) delta)) bs = map (lp_cut_map (\<lambda>t. lp_ieval t nu)) bs"
      using mgu dt dn unfolding mgu_resolve_def by blast
    show "\<exists>d. (\<forall>x. D (d x)) \<and> lp_isubst (lp_isubst a ?s) d = lp_isubst a tau \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t ?s) d)) gs =
      map (lp_cut_map (\<lambda>t. lp_isubst t tau)) gs \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t ?rho) d)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t nu)) bs"
      by (rule exI[of _ "\<lambda>v. delta (lpc_no_swap x y v)"])
        (use factor dd in \<open>simp add: lpc_isubst_comp lp_ieval_subst\<close>)
  qed
  have ds: "\<forall>v. D (?s v)" and dr: "\<forall>v. D (?rho v)"
    using mgu unfolding mgu_resolve_def by (auto intro: substitute variables)
  show ?thesis using unifies ds dr factor unfolding mgu_resolve_def by blast
qed

end
end
