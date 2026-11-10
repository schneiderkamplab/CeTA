theory LP_Cut_Domain_NO_Renaming
  imports LP_Cut_Domain_NO_Source
begin

context cut_runtime_domain
begin
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
