theory LP_Cut_Ranked_Erasure
  imports LP_Cut_Ranked_Forward_Unification
begin

text \<open>Erasure returns ranked executions to the unchanged native names.
It preserves the stack structure, including saved substitutions and cut marks.
The inverse on atoms uses both the predicate arity and argument correctness.\<close>
fun cut_unrank_goal :: "('f \<times> nat,(('f \<times> nat) logic_symbol,'v) logic_tree) logic_goal \<Rightarrow>
    ('f,('f logic_symbol,'v) logic_tree) logic_goal" where
  "cut_unrank_goal (LogicAtom a) = LogicAtom (cut_unrank_atom a)"
| "cut_unrank_goal (LogicMeta t) = LogicMeta (cut_unrank_tree t)"
| "cut_unrank_goal (LogicUnify s t) = LogicUnify (cut_unrank_tree s) (cut_unrank_tree t)"
| "cut_unrank_goal (LogicCut m) = LogicCut m"
| "cut_unrank_goal LogicSuccess = LogicSuccess"
| "cut_unrank_goal LogicFailure = LogicFailure"
fun cut_unrank_choice :: "('f \<times> nat,(('f \<times> nat) logic_symbol,'v) logic_tree) logic_choice \<Rightarrow>
    ('f,('f logic_symbol,'v) logic_tree) logic_choice" where
  "cut_unrank_choice (LogicGoals gs) = LogicGoals (map cut_unrank_goal gs)"
| "cut_unrank_choice (LogicClause gs c m) = LogicClause (map cut_unrank_goal gs) c m"
| "cut_unrank_choice (LogicBarrier m) = LogicBarrier m"

lemma cut_rank_unrank_atom:
  assumes "logic_atom_correct snd (logic_tree_arity_correct (logic_symbol_arity snd)) a"
  shows "cut_rank_runtime_atom (cut_unrank_atom a) = a"
  using assms by (cases a)
    (auto simp: cut_rank_runtime_atom_def map_map o_def list_all_iff
      split: prod.splits intro!: map_idI; metis cut_rank_unrank_tree)
lemma cut_unrank_goal_subst:
  "cut_unrank_goal (logic_goal_map (logic_subst s) g) =
    logic_goal_map (logic_subst (cut_unrank_tree \<circ> s)) (cut_unrank_goal g)"
  by (cases g) (simp_all add: cut_unrank_atom_subst cut_unrank_subst)
lemma cut_unrank_goal_eval_bind:
  "cut_unrank_goal (logic_bind_cut m (logic_eval s) (cut_rank_goal g)) =
    logic_bind_cut m (logic_eval (cut_unrank_tree \<circ> s)) g"
  by (cases g)
    (simp_all add: cut_unrank_rank_atom_eval cut_unrank_subst cut_unrank_embed)
lemma cut_unrank_goal_marks[simp]: "logic_goal_marks (cut_unrank_goal g) = logic_goal_marks g"
  by (cases g) simp_all
lemma cut_unrank_choice_marks[simp]: "logic_choice_marks (cut_unrank_choice c) = logic_choice_marks c"
  by (cases c) (auto simp: image_image)
lemma cut_unrank_fresh[simp]:
  "logic_fresh_mark m (map cut_unrank_choice es) = logic_fresh_mark m es"
  by (simp add: logic_fresh_mark_def image_image)
lemma cut_unrank_prune:
  "logic_prune m (map cut_unrank_choice es) = map cut_unrank_choice (logic_prune m es)"
  by (induct es) (auto split: logic_choice.splits)
lemma cut_unrank_admin:
  "logic_admin (map cut_unrank_choice es) = map_option (map cut_unrank_choice) (logic_admin es)"
  by (induct es rule: logic_admin.induct)
    (auto simp: cut_unrank_prune split: logic_goal.splits)
lemma cut_unrank_lower:
  "logic_lower m t gs \<Longrightarrow> logic_lower m (cut_unrank_tree t) (map cut_unrank_goal gs)"
  by (induct rule: logic_lower.induct)
    (auto split: prod.splits intro: logic_lower.intros)
lemma cut_unrank_lower_diverges:
  "logic_lower_diverges t \<Longrightarrow> logic_lower_diverges (cut_unrank_tree t)"
  by (coinduction arbitrary: t)
    (erule logic_lower_diverges.cases; auto dest: cut_unrank_lower)
lemma cut_unrank_rank_goal[simp]: "cut_unrank_goal (cut_rank_runtime_goal g) = g"
  by (cases g) simp_all
lemma cut_unrank_rank_choice[simp]: "cut_unrank_choice (cut_rank_choice c) = c"
  by (cases c) (simp_all add: map_map o_def)

ML \<open>
  val results = @{thms cut_rank_unrank_atom cut_unrank_goal_subst cut_unrank_goal_eval_bind
    cut_unrank_fresh cut_unrank_prune cut_unrank_admin cut_unrank_lower cut_unrank_lower_diverges}
  val _ = if Thm_Deps.has_skip_proof results then error "Ranked erasure: admitted proof" else ()
  val _ = if null (Thm_Deps.all_oracles results) then () else error "Ranked erasure: oracle dependency"
\<close>
end
