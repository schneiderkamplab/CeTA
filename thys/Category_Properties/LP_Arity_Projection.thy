theory LP_Arity_Projection
  imports LP_Arity_Properties
begin

text \<open>Replacing malformed subtrees by a variable gives an arity-correct
solution of equations whose input terms are arity-correct. This is a theorem
about unifiability, not about preservation of termination by restriction.\<close>
primcorec logic_arity_project ::
  "'f arity \<Rightarrow> 'v \<Rightarrow> ('f,'v) logic_tree \<Rightarrow> ('f,'v) logic_tree" where
  "logic_arity_project A z t = (case t of LVar x \<Rightarrow> LVar x |
    LFun f ts \<Rightarrow> if length ts = A f then
      LFun f (map (logic_arity_project A z) ts) else LVar z)"
lemma logic_arity_project_simps[simp]:
  "logic_arity_project A z (LVar x) = LVar x"
  "logic_arity_project A z (LFun f ts) =
    (if length ts = A f then LFun f (map (logic_arity_project A z) ts) else LVar z)"
  by (subst logic_arity_project.code; simp)+
lemma logic_arity_project_correct:
  "logic_tree_arity_correct A (logic_arity_project A z t)"
  by (coinduction arbitrary: t) (case_tac t; auto simp: list_all_iff)
lemma logic_arity_project_identity:
  "logic_tree_arity_correct A t \<Longrightarrow> logic_arity_project A z t = t"
  by (coinduction arbitrary: t)
    (case_tac t; auto simp: list_all_iff list_all2_map1 list_all2_same)
lemma logic_arity_project_subst:
  "logic_tree_arity_correct A t \<Longrightarrow>
    logic_arity_project A z (logic_subst s t) = logic_subst (logic_arity_project A z \<circ> s) t"
  by (coinduction arbitrary: t rule: logic_tree.coinduct_strong)
    (case_tac t; auto simp: list_all_iff list_all2_map1 list_all2_map2 list_all2_same)

fun logic_arity_project_term ::
  "'f arity \<Rightarrow> 'v \<Rightarrow> ('f,'v) fo_term \<Rightarrow> ('f,'v) fo_term" where
  "logic_arity_project_term A z (SVar x) = SVar x"
| "logic_arity_project_term A z (SFun f ts) = (if length ts=A f then
    SFun f (map (logic_arity_project_term A z) ts) else SVar z)"
lemma logic_arity_project_embed:
  "logic_arity_project A z (logic_embed t) = logic_embed (logic_arity_project_term A z t)"
  by (induct t) (auto simp: map_map o_def)
lemma logic_arity_project_finite:
  "logic_finite t \<Longrightarrow> logic_finite (logic_arity_project A z t)"
  by (auto simp: logic_finite_def logic_arity_project_embed)

lemma logic_arity_project_subtree:
  assumes "logic_subtree u (logic_arity_project A z t)"
  shows "\<exists>v. u=logic_arity_project A z v \<and> logic_subtree v t"
  using assms
proof (induct u "logic_arity_project A z t" arbitrary: t rule: logic_subtree.induct)
  case root
  then show ?case by (auto intro: logic_subtree.root)
next
  case (child u ts v f)
  show ?case
  proof (cases t)
    case (LVar x)
    then show ?thesis using child by simp
  next
    case (LFun g vs)
    have len: "length vs = A g" using child LFun by (auto split: if_splits)
    obtain w where w: "w\<in>set vs" "u=logic_arity_project A z w"
      using child LFun len by auto
    obtain q where q: "v=logic_arity_project A z q" "logic_subtree q w"
      using child.hyps(3)[OF w(2)] by blast
    show ?thesis using q w(1) by (auto simp: LFun intro: logic_subtree.child)
  qed
qed
lemma logic_arity_project_rational:
  "logic_rational t \<Longrightarrow> logic_rational (logic_arity_project A z t)"
  unfolding logic_rational_def
  by (rule finite_subset[of _ "logic_arity_project A z ` {u. logic_subtree u t}"])
    (auto dest: logic_arity_project_subtree)

lemma logic_arity_correct_unifier:
  assumes left: "logic_tree_arity_correct A a"
    and right: "logic_tree_arity_correct A b"
    and solution: "logic_subst s a = logic_subst s b"
  shows "logic_subst (logic_arity_project A z \<circ> s) a =
    logic_subst (logic_arity_project A z \<circ> s) b"
  using arg_cong[OF solution, where f="logic_arity_project A z"]
  by (simp add: logic_arity_project_subst[OF left] logic_arity_project_subst[OF right])

lemma logic_arity_unifiable_iff:
  assumes left: "logic_tree_arity_correct A a"
    and right: "logic_tree_arity_correct A b"
    and closed: "\<And>t. D t \<Longrightarrow> D (logic_arity_project A z t)"
  shows "(\<exists>s. logic_substitution_in D s \<and> logic_subst s a = logic_subst s b) \<longleftrightarrow>
    (\<exists>s. logic_substitution_in (\<lambda>t. D t \<and> logic_tree_arity_correct A t) s \<and>
      logic_subst s a = logic_subst s b)"
proof
  assume "\<exists>s. logic_substitution_in D s \<and> logic_subst s a = logic_subst s b"
  then obtain s where dom: "logic_substitution_in D s" and eq: "logic_subst s a = logic_subst s b" by blast
  have dom': "logic_substitution_in (\<lambda>t. D t \<and> logic_tree_arity_correct A t)
      (logic_arity_project A z \<circ> s)"
    using dom closed logic_arity_project_correct by (auto simp: logic_substitution_in_def)
  show "\<exists>s. logic_substitution_in (\<lambda>t. D t \<and> logic_tree_arity_correct A t) s \<and>
      logic_subst s a = logic_subst s b"
    by (intro exI[of _ "logic_arity_project A z \<circ> s"] conjI dom')
      (rule logic_arity_correct_unifier[OF left right eq])
next
  assume "\<exists>s. logic_substitution_in (\<lambda>t. D t \<and> logic_tree_arity_correct A t) s \<and>
    logic_subst s a = logic_subst s b"
  then show "\<exists>s. logic_substitution_in D s \<and> logic_subst s a = logic_subst s b"
    by (auto simp: logic_substitution_in_def)
qed

end
