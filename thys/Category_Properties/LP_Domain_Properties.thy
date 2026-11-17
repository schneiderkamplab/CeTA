theory LP_Domain_Properties
  imports LP_Properties
begin

text \<open>Domain closure is a proved property of finite and rational trees.
In particular, substituting rational values into a rational tree cannot produce
infinitely many distinct subtrees: only finitely many variables occur in it.\<close>

lemma logic_subst_composition:
  "logic_subst s (logic_subst r t) = logic_subst (\<lambda>x. logic_subst s (r x)) t"
  by (coinduction arbitrary: t rule: logic_tree.coinduct_strong)
    (auto simp: list_all2_map1 list_all2_map2 intro!: list.rel_refl split: logic_tree.splits)

lemma logic_subst_arity_correct:
  assumes "logic_tree_arity_correct A t"
    and "\<And>x. logic_tree_arity_correct A (s x)"
  shows "logic_tree_arity_correct A (logic_subst s t)"
  using assms(1)
  apply (coinduction arbitrary: t)
  apply (case_tac t; auto simp: list_all_iff)
  subgoal for x
    using assms(2)[of x]
    by (cases "s x") (auto simp: list_all_iff)
  done

lemma logic_subtree_trans:
  "logic_subtree t s \<Longrightarrow> logic_subtree u t \<Longrightarrow> logic_subtree u s"
  by (induct rule: logic_subtree.induct) (auto intro: logic_subtree.intros)

lemma logic_subst_subtree:
  assumes "logic_subtree u a" "a = logic_subst sigma t"
  shows "(\<exists>v. logic_subtree v t \<and> u = logic_subst sigma v) \<or>
    (\<exists>x. logic_subtree (LVar x) t \<and> logic_subtree u (sigma x))"
  using assms
proof (induct arbitrary: t rule: logic_subtree.induct)
  case (root a)
  then show ?case using logic_subtree.root by blast
next
  case (child v ts u f)
  show ?case
  proof (cases t)
    case (LVar x)
    have "logic_subtree u (sigma x)"
      using child.prems logic_subtree.child[OF child.hyps(1,2), where f=f]
      by (simp add: LVar; metis)
    then show ?thesis using LVar logic_subtree.root by blast
  next
    case (LFun g vs)
    obtain w where w: "w\<in>set vs" "v=logic_subst sigma w"
      using child.hyps(1) child.prems by (auto simp: LFun)
    show ?thesis using child.hyps(3)[OF w(2)] w(1)
      by (auto simp: LFun intro: logic_subtree.child)
  qed
qed

lemma logic_rational_substitution:
  assumes tree: "logic_rational t" and images: "\<And>x. logic_rational (sigma x)"
  shows "logic_rational (logic_subst sigma t)"
proof -
  let ?S = "{u. logic_subtree u t}"
  let ?X = "LVar -` ?S"
  have finiteS: "finite ?S" using tree by (simp add: logic_rational_def)
  have finiteX: "finite ?X"
    by (rule finite_vimageI[OF finiteS]) (auto intro: injI)
  have finite_union: "finite (\<Union>x\<in>?X. {u. logic_subtree u (sigma x)})"
    by (rule finite_UN_I[OF finiteX]) (simp only: images[unfolded logic_rational_def])
  have subset: "{u. logic_subtree u (logic_subst sigma t)} \<subseteq>
    logic_subst sigma ` ?S \<union> (\<Union>x\<in>?X. {u. logic_subtree u (sigma x)})"
    using logic_subst_subtree[where a="logic_subst sigma t" and sigma=sigma and t=t] by blast
  show ?thesis unfolding logic_rational_def
    by (rule finite_subset[OF subset]) (rule finite_UnI[OF finite_imageI[OF finiteS] finite_union])
qed

lemma logic_rational_arguments:
  "logic_rational (LFun f ts) \<Longrightarrow> list_all logic_rational ts"
  unfolding logic_rational_def list_all_iff
  by (intro ballI; rule finite_subset[of _ "{u. logic_subtree u (LFun f ts)}"])
    (auto intro: logic_subtree.child)

end
