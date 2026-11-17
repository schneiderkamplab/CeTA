theory LP_Runtime_MGU
  imports LP_Representation
begin

text \<open>This bridge predicate expresses most-generality on every variable,
using one substitution. Its terms and atoms are the native representations;
the canonical specification will be connected by explicit translations.\<close>
definition lp_runtime_mgu ::
  "(('f,'v) lp_iterm \<Rightarrow> bool) \<Rightarrow>
    ('p \<times> ('f,'v) lp_iterm list) \<Rightarrow> ('p \<times> ('f,'v) lp_iterm list) \<Rightarrow>
    ('v \<Rightarrow> ('f,'v) lp_iterm) \<Rightarrow> bool" where
  "lp_runtime_mgu D a b sigma \<longleftrightarrow>
    (\<forall>x. D (sigma x)) \<and>
    lp_iatom_subst a sigma = lp_iatom_subst b sigma \<and>
    (\<forall>u. (\<forall>x. D (u x)) \<and> lp_iatom_subst a u = lp_iatom_subst b u
      \<longrightarrow> (\<exists>v. (\<forall>x. D (v x)) \<and>
        (\<forall>x. u x = lp_isubst (sigma x) v)))"

lemma lp_runtime_mgu_normalized:
  fixes sigma :: "'v \<Rightarrow> ('f,'v) lp_iterm"
  assumes domain: "\<And>x. D (sigma x)"
    and equation: "lp_iatom_subst a sigma = lp_iatom_subst b sigma"
    and factor: "\<And>u :: 'v \<Rightarrow> ('f,'v) lp_iterm. \<And>x.
      lp_iatom_subst a u = lp_iatom_subst b u \<Longrightarrow> lp_isubst (sigma x) u = u x"
  shows "lp_runtime_mgu D a b sigma"
proof -
  have "\<exists>v. (\<forall>x. D (v x)) \<and> (\<forall>x. u x = lp_isubst (sigma x) v)"
    if "\<forall>x. D (u x)" "lp_iatom_subst a u = lp_iatom_subst b u" for u
    by (intro exI[of _ u]) (simp add: that factor[OF that(2)])
  then show ?thesis unfolding lp_runtime_mgu_def using domain equation by blast
qed

end
