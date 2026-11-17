theory LP_Ranked_MGU_Properties
  imports LP_Arity_Properties
begin

lemma logic_rank_mgu:
  assumes mgu: "logic_mgu D a b s"
  shows "logic_mgu (\<lambda>t. D (logic_unrank_tree t) \<and> logic_tree_arity_correct snd t)
    (logic_atom_map logic_rank_tree a) (logic_atom_map logic_rank_tree b) (logic_rank_tree \<circ> s)"
proof -
  let ?E = "\<lambda>t. D (logic_unrank_tree t) \<and> logic_tree_arity_correct snd t"
  have domain: "logic_substitution_in ?E (logic_rank_tree \<circ> s)"
    using mgu by (auto simp: logic_mgu_def logic_substitution_in_def logic_rank_arity)
  have equation: "logic_atom_map (logic_subst (logic_rank_tree \<circ> s)) (logic_atom_map logic_rank_tree a) =
    logic_atom_map (logic_subst (logic_rank_tree \<circ> s)) (logic_atom_map logic_rank_tree b)"
    using arg_cong[where f="logic_atom_map logic_rank_tree",
      OF conjunct1[OF conjunct2[OF mgu[unfolded logic_mgu_def]]]]
    by (cases a; cases b) (simp add: map_map o_def logic_rank_subst)
  have factor: "\<exists>v. logic_substitution_in ?E v \<and>
      (\<forall>x. u x = logic_subst v ((logic_rank_tree \<circ> s) x))"
    if ud: "logic_substitution_in ?E u"
      and eq: "logic_atom_map (logic_subst u) (logic_atom_map logic_rank_tree a) =
        logic_atom_map (logic_subst u) (logic_atom_map logic_rank_tree b)" for u
  proof -
    have raw_domain: "logic_substitution_in D (logic_unrank_tree \<circ> u)"
      using ud by (simp add: logic_substitution_in_def)
    have raw_equation:
      "logic_atom_map (logic_subst (logic_unrank_tree \<circ> u)) a =
        logic_atom_map (logic_subst (logic_unrank_tree \<circ> u)) b"
      using arg_cong[OF eq, where f="logic_atom_map logic_unrank_tree"]
      by (cases a; cases b) (simp add: map_map o_def logic_unrank_subst)
    obtain v where v: "logic_substitution_in D v"
      "\<And>x. logic_unrank_tree (u x) = logic_subst v (s x)"
      using mgu raw_domain raw_equation unfolding logic_mgu_def by auto
    have factor_x: "u x = logic_subst (logic_rank_tree \<circ> v) (logic_rank_tree (s x))" for x
      using logic_rank_unrank[of "u x"] v(2)[of x] ud
      by (simp add: logic_substitution_in_def logic_rank_subst)
    show ?thesis by (intro exI[of _ "logic_rank_tree \<circ> v"])
      (simp add: logic_substitution_in_def v(1)[unfolded logic_substitution_in_def]
        logic_rank_arity factor_x)
  qed
  show ?thesis unfolding logic_mgu_def using domain equation factor by blast
qed

lemma logic_rank_mgu_reflect:
  assumes mgu: "logic_mgu (\<lambda>t. D (logic_unrank_tree t) \<and> logic_tree_arity_correct snd t)
    (logic_atom_map logic_rank_tree a) (logic_atom_map logic_rank_tree b) (logic_rank_tree \<circ> s)"
  shows "logic_mgu D a b s"
proof -
  let ?E = "\<lambda>t. D (logic_unrank_tree t) \<and> logic_tree_arity_correct snd t"
  have domain: "logic_substitution_in D s"
    using mgu by (auto simp: logic_mgu_def logic_substitution_in_def)
  have ranked_equation:
    "logic_atom_map (logic_subst (logic_rank_tree \<circ> s)) (logic_atom_map logic_rank_tree a) =
      logic_atom_map (logic_subst (logic_rank_tree \<circ> s)) (logic_atom_map logic_rank_tree b)"
    using mgu unfolding logic_mgu_def by blast
  have equation: "logic_atom_map (logic_subst s) a = logic_atom_map (logic_subst s) b"
    using arg_cong[OF ranked_equation, where f="logic_atom_map logic_unrank_tree"]
    by (cases a; cases b) (simp add: map_map o_def logic_unrank_subst)
  have factor: "\<exists>v. logic_substitution_in D v \<and> (\<forall>x. u x = logic_subst v (s x))"
    if ud: "logic_substitution_in D u"
      and eq: "logic_atom_map (logic_subst u) a = logic_atom_map (logic_subst u) b" for u
  proof -
    have ranked_domain: "logic_substitution_in ?E (logic_rank_tree \<circ> u)"
      using ud by (simp add: logic_substitution_in_def logic_rank_arity)
    have ranked_match:
      "logic_atom_map (logic_subst (logic_rank_tree \<circ> u)) (logic_atom_map logic_rank_tree a) =
        logic_atom_map (logic_subst (logic_rank_tree \<circ> u)) (logic_atom_map logic_rank_tree b)"
      using arg_cong[OF eq, where f="logic_atom_map logic_rank_tree"]
      by (cases a; cases b) (simp add: map_map o_def logic_rank_subst)
    obtain v where vd: "logic_substitution_in ?E v"
      and factor: "\<And>x. logic_rank_tree (u x) = logic_subst v (logic_rank_tree (s x))"
      using mgu ranked_domain ranked_match unfolding logic_mgu_def by auto
    have raw_factor: "u x = logic_subst (logic_unrank_tree \<circ> v) (s x)" for x
      using arg_cong[OF factor[of x], where f=logic_unrank_tree]
      by (simp add: logic_unrank_subst)
    show ?thesis by (intro exI[of _ "logic_unrank_tree \<circ> v"])
      (use vd raw_factor in \<open>auto simp: logic_substitution_in_def\<close>)
  qed
  show ?thesis using domain equation factor unfolding logic_mgu_def by blast
qed

lemma logic_rank_mgu_iff:
  "logic_mgu (\<lambda>t. D (logic_unrank_tree t) \<and> logic_tree_arity_correct snd t)
      (logic_atom_map logic_rank_tree a) (logic_atom_map logic_rank_tree b) (logic_rank_tree \<circ> s)
    \<longleftrightarrow> logic_mgu D a b s"
  using logic_rank_mgu logic_rank_mgu_reflect by blast

fun logic_tag_atom :: "('p,'t) logic_atom \<Rightarrow> ('p \<times> nat,'t) logic_atom" where
  "logic_tag_atom (LAtom p ts) = LAtom (p,length ts) ts"
lemma logic_tag_unification:
  "logic_atom_map f (logic_tag_atom a) = logic_atom_map f (logic_tag_atom b) \<longleftrightarrow>
    logic_atom_map f a = logic_atom_map f b"
  by (cases a; cases b) (auto dest: arg_cong[where f=length])
lemma logic_tag_mgu:
  "logic_mgu D (logic_tag_atom a) (logic_tag_atom b) s \<longleftrightarrow> logic_mgu D a b s"
  by (simp add: logic_mgu_def logic_tag_unification)

definition logic_rank_runtime_atom ::
  "('f,('f,'v) logic_tree) logic_atom \<Rightarrow> ('f \<times> nat,('f \<times> nat,'v) logic_tree) logic_atom" where
  "logic_rank_runtime_atom a = logic_tag_atom (logic_atom_map logic_rank_tree a)"
lemma logic_rank_runtime_atom_correct:
  "logic_atom_correct snd (logic_tree_arity_correct snd) (logic_rank_runtime_atom a)"
  by (cases a) (simp add: logic_rank_runtime_atom_def list_all_iff logic_rank_arity)
lemma logic_rank_runtime_atom_mgu:
  "logic_mgu (\<lambda>t. D (logic_unrank_tree t) \<and> logic_tree_arity_correct snd t)
      (logic_rank_runtime_atom a) (logic_rank_runtime_atom b) (logic_rank_tree \<circ> s)
    \<longleftrightarrow> logic_mgu D a b s"
  by (simp add: logic_rank_runtime_atom_def logic_tag_mgu logic_rank_mgu_iff)

end
