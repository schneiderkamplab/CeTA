theory LP_Arity_MGU_Properties
  imports Category_Properties.LP_Freshening_Properties
begin

text \<open>Substitution cannot repair a malformed function application. If an
unrestricted most-general unifier has an arity-correct instance, its own images
are therefore arity-correct. Projection then supplies arity-correct factors.
This proves the restriction needed for native witnesses without assuming that
restriction preserves termination.\<close>
lemma logic_subst_arity_reflect:
  "logic_tree_arity_correct A (logic_subst s t) \<Longrightarrow> logic_tree_arity_correct A t"
  by (coinduction arbitrary: t) (case_tac t; auto simp: list_all_iff)

lemma logic_mgu_restrict_arity:
  assumes mgu: "logic_mgu D a b s"
    and solution: "logic_substitution_in (\<lambda>t. D t \<and> logic_tree_arity_correct A t) u"
    and equation: "logic_atom_map (logic_subst u) a = logic_atom_map (logic_subst u) b"
    and closed: "\<And>t. D t \<Longrightarrow> D (logic_arity_project A z t)"
  shows "logic_mgu (\<lambda>t. D t \<and> logic_tree_arity_correct A t) a b s"
proof -
  have ud: "logic_substitution_in D u"
    using solution by (auto simp: logic_substitution_in_def)
  obtain v where inst: "\<And>x. u x = logic_subst v (s x)"
    using mgu ud equation unfolding logic_mgu_def by blast
  have uc: "logic_tree_arity_correct A (u x)" for x
    using solution unfolding logic_substitution_in_def by blast
  have correct: "logic_tree_arity_correct A (s x)" for x
    by (rule logic_subst_arity_reflect[where s=v])
      (use uc[of x] in \<open>simp only: inst\<close>)
  have domain: "logic_substitution_in (\<lambda>t. D t \<and> logic_tree_arity_correct A t) s"
    using mgu correct by (auto simp: logic_mgu_def logic_substitution_in_def)
  have eq: "logic_atom_map (logic_subst s) a = logic_atom_map (logic_subst s) b"
    using mgu unfolding logic_mgu_def by blast
  have factors: "\<exists>v. logic_substitution_in (\<lambda>t. D t \<and> logic_tree_arity_correct A t) v \<and>
      (\<forall>x. w x = logic_subst v (s x))"
    if wd: "logic_substitution_in (\<lambda>t. D t \<and> logic_tree_arity_correct A t) w"
      and we: "logic_atom_map (logic_subst w) a = logic_atom_map (logic_subst w) b" for w
  proof -
    have raw: "logic_substitution_in D w" using wd by (auto simp: logic_substitution_in_def)
    obtain v where vd: "logic_substitution_in D v" and vf: "\<And>x. w x = logic_subst v (s x)"
      using mgu raw we unfolding logic_mgu_def by blast
    have pd: "logic_substitution_in (\<lambda>t. D t \<and> logic_tree_arity_correct A t)
        (logic_arity_project A z \<circ> v)"
      using vd closed logic_arity_project_correct by (auto simp: logic_substitution_in_def)
    have pf: "w x = logic_subst (logic_arity_project A z \<circ> v) (s x)" for x
      using arg_cong[OF vf[of x], where f="logic_arity_project A z"] wd
      by (simp add: logic_substitution_in_def logic_arity_project_identity
        logic_arity_project_subst[OF correct])
    show ?thesis by (intro exI[of _ "logic_arity_project A z \<circ> v"] conjI pd allI pf)
  qed
  show ?thesis using domain eq factors unfolding logic_mgu_def by blast
qed

lemma logic_mgu_correct_arity:
  assumes mgu: "logic_mgu D a b s"
    and left: "list_all (logic_tree_arity_correct A) (logic_arguments a)"
    and right: "list_all (logic_tree_arity_correct A) (logic_arguments b)"
    and closed: "\<And>t. D t \<Longrightarrow> D (logic_arity_project A z t)"
  shows "logic_mgu (\<lambda>t. D t \<and> logic_tree_arity_correct A t) a b s"
proof -
  have domain: "logic_substitution_in (\<lambda>t. D t \<and> logic_tree_arity_correct A t)
      (logic_arity_project A z \<circ> s)"
    using mgu closed logic_arity_project_correct by (auto simp: logic_mgu_def logic_substitution_in_def)
  have eq: "logic_atom_map (logic_subst s) a = logic_atom_map (logic_subst s) b"
    using mgu unfolding logic_mgu_def by blast
  have projected: "logic_atom_map (logic_subst (logic_arity_project A z \<circ> s)) a =
      logic_atom_map (logic_subst (logic_arity_project A z \<circ> s)) b"
    using arg_cong[OF eq, where f="logic_atom_map (logic_arity_project A z)"]
    by (simp only: logic_atom_arity_project_subst[OF left] logic_atom_arity_project_subst[OF right])
  show ?thesis by (rule logic_mgu_restrict_arity[OF mgu domain projected closed])
qed

end
