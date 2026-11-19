theory LP_Fresh_MGU_Context
  imports LP_Checked_Global_MGU Category_Properties.LP_Variables_Properties
begin

lemma lp_runtime_subst_on_variables:
  fixes s r :: "'v \<Rightarrow> ('f,'v) lp_iterm"
  assumes same: "\<And>x. x\<in>lp_runtime_variables t \<Longrightarrow> s x = r x"
  shows "lp_isubst t s = lp_isubst t r"
proof -
  have eq: "logic_subst (logic_from_native \<circ> s) (logic_from_native t) =
      logic_subst (logic_from_native \<circ> r) (logic_from_native t)"
    by (rule logic_subst_on_variables) (simp add: o_def same lp_runtime_variables_def)
  show ?thesis using arg_cong[OF eq, where f=logic_to_native]
    by (simp add: logic_subst_translation o_def)
qed

lemma lp_merge_fresh_substitutions:
  fixes r :: "'v \<Rightarrow> 'v" and s t :: "'v \<Rightarrow> 'a"
  assumes injective: "inj_on r Y" and disjoint: "r ` Y \<inter> X = {}"
    and sd: "\<And>x. D (s x)" and td: "\<And>x. D (t x)"
  obtains u where "\<And>x. D (u x)" "\<And>x. x \<in> X \<Longrightarrow> u x = s x"
    "\<And>x. x \<in> Y \<Longrightarrow> u (r x) = t x"
proof -
  let ?u = "\<lambda>x. if x \<in> r ` Y then t (inv_into Y r x) else s x"
  have domain: "D (?u x)" for x using sd td by simp
  have caller: "?u x = s x" if "x \<in> X" for x using disjoint that by auto
  have clause: "?u (r x) = t x" if "x \<in> Y" for x
    using injective that by (simp add: inv_into_f_f)
  show thesis by (rule that[OF domain caller clause])
qed

lemma lp_fresh_resolution_factors_context:
  fixes tau nu :: "'v \<Rightarrow> ('f,'v) lp_iterm"
  assumes fresh: "lp_fresh_resolution D a gs h bs sigma rho"
    and dt: "\<And>x. D (tau x)" and dn: "\<And>x. D (nu x)"
    and equation: "lp_isubst a tau = lp_ieval h nu"
  obtains delta where "\<And>x. D (delta x)"
    "\<And>t. t\<in>set (a # concat (map lp_cut_terms gs)) \<Longrightarrow>
      lp_isubst (lp_isubst t sigma) delta = lp_isubst t tau"
    "\<And>t. t\<in>set (h # concat (map lp_cut_terms bs)) \<Longrightarrow>
      lp_isubst (lp_ieval t rho) delta = lp_ieval t nu"
proof -
  let ?X = "\<Union>(lp_runtime_variables ` set (a # concat (map lp_cut_terms gs)))"
  let ?Y = "\<Union>(vars_term ` set (h # concat (map lp_cut_terms bs)))"
  obtain r where fresh: "inj_on r ?Y" "r ` ?Y \<inter> ?X = {}"
    and rho: "rho = sigma \<circ> r"
    and mgu: "lp_runtime_mgu D ((),[a]) ((),[lp_ieval h (LPIVar \<circ> r)]) sigma"
    using fresh unfolding lp_fresh_resolution_def lp_runtime_freshening_def Let_def by blast
  obtain u where du: "\<And>x. D (u x)"
    and caller: "\<And>x. x\<in>?X \<Longrightarrow> u x = tau x"
    and clause: "\<And>x. x\<in>?Y \<Longrightarrow> u (r x) = nu x"
    by (rule lp_merge_fresh_substitutions[where s=tau and t=nu and D=D, OF fresh dt dn]) blast
  have active: "lp_isubst t u = lp_isubst t tau"
    if "t\<in>set (a # concat (map lp_cut_terms gs))" for t
    by (rule lp_runtime_subst_on_variables) (use caller that in auto)
  have body: "lp_ieval t (u \<circ> r) = lp_ieval t nu"
    if "t\<in>set (h # concat (map lp_cut_terms bs))" for t
    by (rule lp_ieval_cong) (use clause that in \<open>auto simp: o_def\<close>)
  have unified: "lp_iatom_subst ((),[a]) u =
      lp_iatom_subst ((),[lp_ieval h (LPIVar \<circ> r)]) u"
    using equation active[of a] body[of h]
    by (simp add: lp_iatom_subst_def lp_ieval_subst o_def)
  obtain delta where dd: "\<And>x. D (delta x)"
    and factor: "\<And>x. u x = lp_isubst (sigma x) delta"
    using mgu du unified unfolding lp_runtime_mgu_def by blast
  have composition: "(\<lambda>x. lp_isubst (sigma x) delta) = u"
    using factor by auto
  have caller_factor: "lp_isubst (lp_isubst t sigma) delta = lp_isubst t tau"
    if "t\<in>set (a # concat (map lp_cut_terms gs))" for t
    by (simp add: lpc_isubst_comp composition active[OF that])
  have clause_factor: "lp_isubst (lp_ieval t rho) delta = lp_ieval t nu"
    if "t\<in>set (h # concat (map lp_cut_terms bs))" for t
    by (simp add: lp_ieval_subst rho o_def factor[symmetric] body[OF that, unfolded o_def])
  show thesis by (rule that[OF dd caller_factor clause_factor])
qed

end
