theory LP_Tree_Countability
  imports LP_MGU_Arity_Abstraction "HOL-Library.Countable_Set"
begin

text \<open>Each finitely branching runtime tree has only countably many
subtrees, even when its depth is infinite. A countable substitution therefore
needs only countably many names for malformed subtrees.\<close>
fun logic_tree_level :: "('f,'v) logic_tree \<Rightarrow> nat \<Rightarrow> ('f,'v) logic_tree set" where
  "logic_tree_level t 0 = {t}"
| "logic_tree_level t (Suc n) = (case t of LVar x \<Rightarrow> {} |
    LFun f ts \<Rightarrow> \<Union>(set (map (\<lambda>u. logic_tree_level u n) ts)))"
lemma finite_logic_tree_level: "finite (logic_tree_level t n)"
  by (induct n arbitrary: t) (auto split: logic_tree.splits)
lemma logic_subtree_level:
  "logic_subtree u t \<Longrightarrow> \<exists>n. u \<in> logic_tree_level t n"
proof (induct rule: logic_subtree.induct)
  case (root t)
  show ?case by (rule exI[of _ 0]) simp
next
  case (child u ts v f)
  then obtain n where "v \<in> logic_tree_level u n" by blast
  then show ?case using child.hyps(1) by (intro exI[of _ "Suc n"]) auto
qed
lemma countable_logic_subtrees: "countable {u. logic_subtree u t}"
proof (rule countable_subset)
  show "{u. logic_subtree u t} \<subseteq> (\<Union>n. logic_tree_level t n)"
    using logic_subtree_level by blast
  show "countable (\<Union>n. logic_tree_level t n)"
    by (intro countable_UN countableI_type countable_finite finite_logic_tree_level)
qed
lemma countable_logic_substitution_subtrees:
  fixes s :: "'v::countable \<Rightarrow> ('f,'w) logic_tree"
  shows "countable (\<Union>x. {u. logic_subtree u (s x)})"
  by (simp add: countable_logic_subtrees)

ML \<open>
  val results = @{thms countable_logic_subtrees countable_logic_substitution_subtrees}
  val _ = if Thm_Deps.has_skip_proof results then error "Tree countability: admitted proof" else ()
  val _ = if null (Thm_Deps.all_oracles results) then () else error "Tree countability: oracle dependency"
\<close>
end
