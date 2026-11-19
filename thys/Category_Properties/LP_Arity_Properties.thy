theory LP_Arity_Properties
  imports LP_Domain_Properties
begin

text \<open>The boundary represents each raw symbol occurrence by its name and
argument count. Erasure is inverse on trees respecting arity snd. This is an
explicit encoding, not a signature-restriction termination argument.\<close>

primcorec logic_rank_tree :: "('f,'v) logic_tree \<Rightarrow> ('f \<times> nat,'v) logic_tree" where
  "logic_rank_tree t = (case t of LVar x \<Rightarrow> LVar x |
    LFun f ts \<Rightarrow> LFun (f,length ts) (map logic_rank_tree ts))"
primcorec logic_unrank_tree :: "('f \<times> nat,'v) logic_tree \<Rightarrow> ('f,'v) logic_tree" where
  "logic_unrank_tree t = (case t of LVar x \<Rightarrow> LVar x |
    LFun f ts \<Rightarrow> LFun (fst f) (map logic_unrank_tree ts))"

lemma logic_rank_simps[simp]:
  "logic_rank_tree (LVar x) = LVar x"
  "logic_rank_tree (LFun f ts) = LFun (f,length ts) (map logic_rank_tree ts)"
  by (subst logic_rank_tree.code; simp)+
lemma logic_unrank_simps[simp]:
  "logic_unrank_tree (LVar x) = LVar x"
  "logic_unrank_tree (LFun f ts) = LFun (fst f) (map logic_unrank_tree ts)"
  by (subst logic_unrank_tree.code; simp)+
lemma logic_unrank_rank[simp]: "logic_unrank_tree (logic_rank_tree t) = t"
  by (coinduction arbitrary: t)
    (case_tac t; auto simp: list_all2_map1 intro!: list.rel_refl)
lemma logic_rank_arity: "logic_tree_arity_correct snd (logic_rank_tree t)"
  by (coinduction arbitrary: t) (case_tac t; auto simp: list_all_iff)
lemma logic_rank_subst:
  "logic_rank_tree (logic_subst s t) = logic_subst (logic_rank_tree \<circ> s) (logic_rank_tree t)"
  by (coinduction arbitrary: t rule: logic_tree.coinduct_strong)
    (case_tac t; auto simp: list_all2_map1 list_all2_map2 intro!: list.rel_refl)
lemma logic_unrank_subst:
  "logic_unrank_tree (logic_subst s t) = logic_subst (logic_unrank_tree \<circ> s) (logic_unrank_tree t)"
  by (coinduction arbitrary: t rule: logic_tree.coinduct_strong)
    (case_tac t; auto simp: list_all2_map1 list_all2_map2 intro!: list.rel_refl)

lemma logic_rank_unrank:
  assumes "logic_tree_arity_correct snd t"
  shows "logic_rank_tree (logic_unrank_tree t) = t"
  using assms
  by (coinduction arbitrary: t)
    (case_tac t; auto simp: list_all_iff list_all2_map1 list_all2_same)

fun logic_rank_term :: "('f,'v) fo_term \<Rightarrow> ('f \<times> nat,'v) fo_term" where
  "logic_rank_term (SVar x) = SVar x"
| "logic_rank_term (SFun f ts) = SFun (f,length ts) (map logic_rank_term ts)"
fun logic_unrank_term :: "('f \<times> nat,'v) fo_term \<Rightarrow> ('f,'v) fo_term" where
  "logic_unrank_term (SVar x) = SVar x"
| "logic_unrank_term (SFun f ts) = SFun (fst f) (map logic_unrank_term ts)"

lemma logic_rank_embed:
  "logic_rank_tree (logic_embed t) = logic_embed (logic_rank_term t)"
  by (induct t) (auto simp: map_map intro!: map_cong)
lemma logic_unrank_embed:
  "logic_unrank_tree (logic_embed t) = logic_embed (logic_unrank_term t)"
  by (induct t) (auto simp: map_map intro!: map_cong)
lemma logic_rank_finite:
  "logic_finite (logic_rank_tree t) \<longleftrightarrow> logic_finite t"
proof
  assume "logic_finite (logic_rank_tree t)"
  then obtain u where "logic_rank_tree t = logic_embed u" by (auto simp: logic_finite_def)
  then have "t = logic_embed (logic_unrank_term u)"
    by (metis logic_unrank_rank logic_unrank_embed)
  then show "logic_finite t" by (auto simp: logic_finite_def)
next
  assume "logic_finite t"
  then show "logic_finite (logic_rank_tree t)" by (auto simp: logic_finite_def logic_rank_embed)
qed

lemma logic_rank_subtree:
  assumes "logic_subtree u (logic_rank_tree t)"
  shows "\<exists>v. u = logic_rank_tree v \<and> logic_subtree v t"
  using assms
proof (induct u "logic_rank_tree t" arbitrary: t rule: logic_subtree.induct)
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
    obtain w where w: "w \<in> set vs" "u = logic_rank_tree w"
      using child by (auto simp: LFun)
    obtain z where z: "v = logic_rank_tree z" "logic_subtree z w"
      using child.hyps(3)[OF w(2)] by blast
    show ?thesis using z w(1)
      by (auto simp: LFun intro: logic_subtree.child)
  qed
qed

lemma logic_unrank_subtree:
  assumes "logic_subtree u (logic_unrank_tree t)"
  shows "\<exists>v. u = logic_unrank_tree v \<and> logic_subtree v t"
  using assms
proof (induct u "logic_unrank_tree t" arbitrary: t rule: logic_subtree.induct)
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
    obtain w where w: "w \<in> set vs" "u = logic_unrank_tree w"
      using child by (auto simp: LFun)
    obtain z where z: "v = logic_unrank_tree z" "logic_subtree z w"
      using child.hyps(3)[OF w(2)] by blast
    show ?thesis using z w(1)
      by (auto simp: LFun intro: logic_subtree.child)
  qed
qed

lemma logic_rank_rational_forward:
  "logic_rational t \<Longrightarrow> logic_rational (logic_rank_tree t)"
  unfolding logic_rational_def
  by (rule finite_subset[of _ "logic_rank_tree ` {u. logic_subtree u t}"])
    (auto dest: logic_rank_subtree)
lemma logic_unrank_rational:
  "logic_rational t \<Longrightarrow> logic_rational (logic_unrank_tree t)"
  unfolding logic_rational_def
  by (rule finite_subset[of _ "logic_unrank_tree ` {u. logic_subtree u t}"])
    (auto dest: logic_unrank_subtree)
lemma logic_rank_rational:
  "logic_rational (logic_rank_tree t) \<longleftrightarrow> logic_rational t"
  by (metis logic_unrank_rational logic_unrank_rank logic_rank_rational_forward)

text \<open>Overloaded names become distinct ranked symbols. A mismatched
argument count is rejected even if all arguments themselves are correct.\<close>
lemma logic_rank_overloaded_examples:
  "logic_rank_tree (LFun p [LVar x]) = LFun (p,1) [LVar x]"
  "logic_rank_tree (LFun p [LVar x,LVar y]) = LFun (p,2) [LVar x,LVar y]"
  "\<not> logic_tree_arity_correct snd (LFun (p,1) [])"
  by simp_all

end
