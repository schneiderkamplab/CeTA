theory LP_Cut_Ranked_Execution
  imports LP_Cut_Ranked_MGU
begin

text \<open>Ranking changes names, not clause indexes, saved alternatives or cut
barriers. Meta-call operands remain trees.\<close>
fun cut_rank_runtime_goal :: "('f,('f logic_symbol,'v) logic_tree) logic_goal \<Rightarrow>
    ('f \<times> nat,(('f \<times> nat) logic_symbol,'v) logic_tree) logic_goal" where
  "cut_rank_runtime_goal (LogicAtom a) = LogicAtom (cut_rank_runtime_atom a)"
| "cut_rank_runtime_goal (LogicMeta t) = LogicMeta (cut_rank_tree t)"
| "cut_rank_runtime_goal (LogicUnify s t) = LogicUnify (cut_rank_tree s) (cut_rank_tree t)"
| "cut_rank_runtime_goal (LogicCut m) = LogicCut m"
| "cut_rank_runtime_goal LogicSuccess = LogicSuccess"
| "cut_rank_runtime_goal LogicFailure = LogicFailure"
fun cut_rank_choice :: "('f,('f logic_symbol,'v) logic_tree) logic_choice \<Rightarrow>
    ('f \<times> nat,(('f \<times> nat) logic_symbol,'v) logic_tree) logic_choice" where
  "cut_rank_choice (LogicGoals gs) = LogicGoals (map cut_rank_runtime_goal gs)"
| "cut_rank_choice (LogicClause gs c m) = LogicClause (map cut_rank_runtime_goal gs) c m"
| "cut_rank_choice (LogicBarrier m) = LogicBarrier m"

lemma cut_rank_goal_embed:
  "cut_rank_runtime_goal (logic_goal_map logic_embed g) =
    logic_goal_map logic_embed (cut_rank_goal g)"
  by (cases g) (simp_all add: cut_rank_runtime_atom_embed cut_rank_embed)
lemma cut_rank_goal_subst:
  "cut_rank_runtime_goal (logic_goal_map (logic_subst s) g) =
    logic_goal_map (logic_subst (cut_rank_tree \<circ> s)) (cut_rank_runtime_goal g)"
  by (cases g) (simp_all add: cut_rank_runtime_atom_subst cut_rank_subst)
lemma cut_rank_goal_marks[simp]:
  "logic_goal_marks (cut_rank_runtime_goal g) = logic_goal_marks g"
  by (cases g) simp_all
lemma cut_rank_choice_marks[simp]:
  "logic_choice_marks (cut_rank_choice c) = logic_choice_marks c"
  by (cases c) (auto simp: image_image)
lemma cut_rank_fresh_mark[simp]:
  "logic_fresh_mark m (map cut_rank_choice es) = logic_fresh_mark m es"
  by (simp add: logic_fresh_mark_def image_image)
lemma cut_rank_prune:
  "logic_prune m (map cut_rank_choice es) = map cut_rank_choice (logic_prune m es)"
  by (induct es) (auto split: logic_choice.splits)
lemma cut_rank_admin:
  "logic_admin (map cut_rank_choice es) = map_option (map cut_rank_choice) (logic_admin es)"
  by (induct es rule: logic_admin.induct)
    (auto simp: cut_rank_prune split: logic_goal.splits)
lemma cut_rank_lower:
  "logic_lower m t gs \<Longrightarrow>
    logic_lower m (cut_rank_tree t) (map cut_rank_runtime_goal gs)"
  by (induct rule: logic_lower.induct)
    (auto simp: cut_rank_runtime_atom_def intro: logic_lower.intros)

lemma cut_rank_bind:
  "cut_rank_runtime_goal (logic_bind_cut m (logic_subst s) g) =
    logic_bind_cut m (logic_subst (cut_rank_tree \<circ> s)) (cut_rank_runtime_goal g)"
  by (cases g) (simp_all add: cut_rank_runtime_atom_subst cut_rank_subst)
lemma cut_rank_atom_selectors[simp]:
  "logic_predicate (cut_rank_atom a) = (logic_predicate a,length (logic_arguments a))"
  "logic_arguments (cut_rank_atom a) = map cut_rank_term (logic_arguments a)"
  by (cases a; simp)+
lemma cut_rank_slice:
  "logic_slice (cut_rank_program P) (f,n) n = logic_slice P f n"
  by (auto simp: logic_slice_def cut_rank_program_def case_prod_unfold
    split: logic_atom.splits intro!: filter_cong)
lemma cut_rank_lower_diverges:
  "logic_lower_diverges t \<Longrightarrow> logic_lower_diverges (cut_rank_tree t)"
  by (coinduction arbitrary: t)
    (erule logic_lower_diverges.cases; auto dest: cut_rank_lower)

text \<open>These control steps require no unification hypothesis. They preserve
both clause order and the caller's saved alternatives.\<close>
lemma cut_rank_admin_step:
  "logic_admin es = Some fs \<Longrightarrow>
    logic_cut_step snd D (cut_rank_program P) (map cut_rank_choice es) (map cut_rank_choice fs)"
  by (rule logic_cut_step.admin) (simp add: cut_rank_admin)
lemma cut_rank_meta_diverges_step:
  "logic_lower_diverges a \<Longrightarrow>
    logic_cut_step snd D (cut_rank_program P)
      (map cut_rank_choice (LogicGoals (LogicMeta a#gs)#es))
      (map cut_rank_choice (LogicGoals (LogicMeta a#gs)#es))"
  by (simp add: logic_cut_step.meta_diverges cut_rank_lower_diverges)

lemma cut_rank_subtree:
  "logic_subtree u t \<Longrightarrow> logic_subtree (cut_rank_tree u) (cut_rank_tree t)"
  by (induct rule: logic_subtree.induct) (fastforce intro: logic_subtree.intros)+
lemma cut_rank_variables[simp]: "logic_variables (cut_rank_tree t) = logic_variables t"
proof -
  have forward: "logic_subtree (LVar x) (cut_rank_tree t) \<Longrightarrow> logic_subtree (LVar x) t" for x
  proof -
    assume premise: "logic_subtree (LVar x) (cut_rank_tree t)"
    obtain u where u: "LVar x = cut_rank_tree u" "logic_subtree u t"
      using logic_relabel_subtree[OF cut_rank_tree_simps(1) cut_rank_tree_simps(2) premise] by blast
    show ?thesis using u by (cases u) auto
  qed
  show ?thesis unfolding logic_variables_def
    using forward cut_rank_subtree[of "LVar _" t] by auto
qed
lemma cut_rank_freshening:
  "logic_freshening r (map cut_rank_tree active) (map cut_rank_term clause) =
    logic_freshening r active clause"
  by (simp add: logic_freshening_def image_image o_def cut_rank_embed[symmetric])

ML \<open>
  val results = @{thms cut_rank_goal_embed cut_rank_goal_subst cut_rank_fresh_mark
    cut_rank_prune cut_rank_admin cut_rank_lower cut_rank_slice cut_rank_lower_diverges cut_rank_admin_step cut_rank_meta_diverges_step cut_rank_freshening}
  val _ = if Thm_Deps.has_skip_proof results then error "Cut ranking: admitted proof" else ()
  val _ = if null (Thm_Deps.all_oracles results) then () else error "Cut ranking: oracle dependency"
\<close>
end
