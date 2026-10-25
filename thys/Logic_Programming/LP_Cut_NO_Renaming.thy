theory LP_Cut_NO_Renaming
  imports LP_Cut_MGU_Normalize
begin

text \<open>Changing the names of the output variables of an MGU preserves
most-generality. Only the active continuation is renamed; saved alternatives
are independent and remain unchanged. A swap is a total bijection, including
variables not mentioned in the selected atom.\<close>

definition lpc_no_swap where
  "lpc_no_swap x y z = (if z=x then y else if z=y then x else z)"

lemma lpc_no_swap_inverse[simp]:
  "lpc_no_swap x y (lpc_no_swap x y z) = z"
  by (auto simp: lpc_no_swap_def)

lemma lpc_no_swap_factor:
  "lp_isubst (lp_isubst t (\<lambda>v. LPIVar (lpc_no_swap x y v)))
     (\<lambda>v. delta (lpc_no_swap x y v)) = lp_isubst t delta"
  by (simp add: lpc_isubst_comp)

lemma lpc_mgu_resolve_output_swap:
  fixes a :: "('f,string) lp_iterm"
  assumes mgu: "lpc_mgu_resolve a gs h bs sigma rho"
  shows "lpc_mgu_resolve a gs h bs
    (\<lambda>v. lp_isubst (sigma v) (\<lambda>w. LPIVar (lpc_no_swap x y w)))
    (\<lambda>v. lp_isubst (rho v) (\<lambda>w. LPIVar (lpc_no_swap x y w)))"
proof -
  let ?r = "\<lambda>w. LPIVar (lpc_no_swap x y w)"
  let ?s = "\<lambda>v. lp_isubst (sigma v) ?r"
  let ?rho = "\<lambda>v. lp_isubst (rho v) ?r"
  have unifies: "lp_isubst a ?s = lp_ieval h ?rho"
    using arg_cong[OF conjunct1[OF mgu[unfolded lpc_mgu_resolve_def]],
      of "\<lambda>t. lp_isubst t (\<lambda>w. LPIVar (lpc_no_swap x y w))"]
    by (simp add: lpc_isubst_comp lp_ieval_subst)
  have factor: "\<forall>(tau :: string \<Rightarrow> ('f,string) lp_iterm) nu. lp_isubst a tau = lp_ieval h nu \<longrightarrow>
    (\<exists>delta. lp_isubst (lp_isubst a ?s) delta = lp_isubst a tau \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t ?s) delta)) gs =
      map (lp_cut_map (\<lambda>t. lp_isubst t tau)) gs \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t ?rho) delta)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t nu)) bs)"
  proof (intro allI impI)
    fix tau nu :: "string \<Rightarrow> ('f,string) lp_iterm"
    assume "lp_isubst a tau = lp_ieval h nu"
    then obtain delta where factor:
      "lp_isubst (lp_isubst a sigma) delta = lp_isubst a tau"
      "map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t sigma) delta)) gs = map (lp_cut_map (\<lambda>t. lp_isubst t tau)) gs"
      "map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t rho) delta)) bs = map (lp_cut_map (\<lambda>t. lp_ieval t nu)) bs"
      using mgu unfolding lpc_mgu_resolve_def by blast
    show "\<exists>d. lp_isubst (lp_isubst a ?s) d = lp_isubst a tau \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_isubst t ?s) d)) gs =
      map (lp_cut_map (\<lambda>t. lp_isubst t tau)) gs \<and>
      map (lp_cut_map (\<lambda>t. lp_isubst (lp_ieval t ?rho) d)) bs =
      map (lp_cut_map (\<lambda>t. lp_ieval t nu)) bs"
      by (rule exI[of _ "\<lambda>v. delta (lpc_no_swap x y v)"])
        (use factor in \<open>simp add: lpc_isubst_comp lp_ieval_subst\<close>)
  qed
  show ?thesis using unifies factor by (simp only: lpc_mgu_resolve_def)
qed

end
