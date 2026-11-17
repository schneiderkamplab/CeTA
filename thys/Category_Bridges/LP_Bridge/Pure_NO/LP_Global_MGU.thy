theory LP_Global_MGU
  imports LP_Unification_Factorisation Category_LP_Bridge.LP_Runtime_MGU
begin

text \<open>The finite unification algorithm supplies a normalized MGU: every
unifier is unchanged by composing it after the result. This stronger property
provides a domain-correct factor simply by choosing the competing unifier.\<close>
definition lp_normalized_mgu ::
  "('f,string) lp_atom \<Rightarrow> ('f,string) lp_atom \<Rightarrow>
    (string \<Rightarrow> ('f,string) term) \<Rightarrow> bool" where
  "lp_normalized_mgu a b sigma \<longleftrightarrow>
    lp_atom_subst a sigma = lp_atom_subst b sigma \<and>
    (\<forall>u :: string \<Rightarrow> ('f,string) lp_iterm.
      lp_atom_eval a u = lp_atom_eval b u \<longrightarrow>
        (\<forall>x. lp_ieval (sigma x) u = u x))"

lemma lp_normalized_mgu_exists:
  fixes a b :: "('f,string) lp_atom"
    and theta :: "string \<Rightarrow> ('f,string) term"
  assumes solution: "lp_atom_subst a theta = lp_atom_subst b theta"
  obtains sigma where "lp_normalized_mgu a b sigma"
proof -
  have match: "Fun (fst a) (snd a) \<cdot> theta = Fun (fst b) (snd b) \<cdot> theta"
    using solution by (simp add: lp_atom_subst_def)
  obtain sigma where unified: "Fun (fst a) (snd a) \<cdot> sigma = Fun (fst b) (snd b) \<cdot> sigma"
    and factor: "\<And>(u :: string \<Rightarrow> ('f,string) lp_iterm) x.
      lp_ieval (Fun (fst a) (snd a)) u = lp_ieval (Fun (fst b) (snd b)) u
      \<Longrightarrow> lp_ieval (sigma x) u = u x"
    by (rule lp_finite_solution_universal_mgu[OF match]) blast
  have "lp_normalized_mgu a b sigma"
    unfolding lp_normalized_mgu_def
    using unified factor by (auto simp: lp_atom_subst_def lp_atom_eval_def)
  then show thesis by (rule that)
qed

lemma lp_normalized_mgu_finite_factor:
  fixes theta :: "string \<Rightarrow> ('f,string) term"
  assumes mgu: "lp_normalized_mgu a b sigma"
    and solution: "lp_atom_subst a theta = lp_atom_subst b theta"
  shows "sigma x \<cdot> theta = theta x"
proof -
  have eq: "lp_atom_eval a (\<lambda>x. lp_ieval (theta x) LPIVar) =
    lp_atom_eval b (\<lambda>x. lp_ieval (theta x) LPIVar)"
    using arg_cong[OF solution, where f="\<lambda>a. lp_atom_eval a LPIVar"]
    by (simp add: lp_atom_subst_def lp_atom_eval_def map_map o_def lp_ieval_finite_subst)
  have "lp_ieval (sigma x) (\<lambda>x. lp_ieval (theta x) LPIVar) = lp_ieval (theta x) LPIVar"
    using mgu eq unfolding lp_normalized_mgu_def by blast
  then show ?thesis by (intro lp_finite_embedding_injective) (simp add: lp_ieval_finite_subst)
qed

lemma lp_normalized_mgu_runtime:
  assumes mgu: "lp_normalized_mgu a b sigma"
    and finite: "\<And>t. D (lp_ieval t LPIVar)"
  shows "lp_runtime_mgu D (lp_atom_eval a LPIVar) (lp_atom_eval b LPIVar)
    (\<lambda>x. lp_ieval (sigma x) LPIVar)"
proof -
  have equation: "lp_iatom_subst (lp_atom_eval a LPIVar) (\<lambda>x. lp_ieval (sigma x) LPIVar) =
    lp_iatom_subst (lp_atom_eval b LPIVar) (\<lambda>x. lp_ieval (sigma x) LPIVar)"
    using arg_cong[where f="\<lambda>a. lp_atom_eval a LPIVar",
      OF conjunct1[OF mgu[unfolded lp_normalized_mgu_def]]]
    by (simp add: lp_iatom_subst_def lp_atom_eval_def lp_atom_subst_def
      map_map o_def lp_ieval_subst lp_ieval_finite_subst)
  have factor: "\<exists>v. (\<forall>x. D (v x)) \<and>
      (\<forall>x. u x = lp_isubst (lp_ieval (sigma x) LPIVar) v)"
    if domain: "\<forall>x. D (u x)"
      and eq: "lp_iatom_subst (lp_atom_eval a LPIVar) u = lp_iatom_subst (lp_atom_eval b LPIVar) u" for u
  proof -
    have "lp_atom_eval a u = lp_atom_eval b u"
      using eq by (simp add: lp_iatom_subst_def lp_atom_eval_def map_map o_def lp_ieval_subst)
    then have "\<forall>x. lp_ieval (sigma x) u = u x"
      using mgu unfolding lp_normalized_mgu_def by blast
    then show ?thesis by (intro exI[of _ u]) (simp add: domain lp_ieval_subst)
  qed
  show ?thesis unfolding lp_runtime_mgu_def using finite equation factor by blast
qed

end
