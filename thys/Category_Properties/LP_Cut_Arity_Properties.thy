theory LP_Cut_Arity_Properties
  imports LP_Cut_Execution_Properties LP_Arity_Projection
begin

text \<open>These predicates and invariants are proof infrastructure. The
specification describes execution independently of its preservation proofs.\<close>
fun logic_runtime_goal_correct ::
  "'f arity \<Rightarrow> ('f,('f logic_symbol,'v) logic_tree) logic_goal \<Rightarrow> bool" where
  "logic_runtime_goal_correct A (LogicAtom a) =
    logic_atom_correct A (logic_tree_arity_correct (logic_symbol_arity A)) a"
| "logic_runtime_goal_correct A g =
    list_all (logic_tree_arity_correct (logic_symbol_arity A)) (logic_goal_terms g)"
fun logic_runtime_choice_correct ::
  "'f arity \<Rightarrow> ('f,('f logic_symbol,'v) logic_tree) logic_choice \<Rightarrow> bool" where
  "logic_runtime_choice_correct A (LogicGoals gs) = list_all (logic_runtime_goal_correct A) gs"
| "logic_runtime_choice_correct A (LogicClause gs c m) = list_all (logic_runtime_goal_correct A) gs"
| "logic_runtime_choice_correct A (LogicBarrier m) = True"
abbreviation logic_runtime_state_correct where
  "logic_runtime_state_correct A es \<equiv> list_all (logic_runtime_choice_correct A) es"

lemma logic_atom_correct_map:
  "logic_atom_correct A T (logic_atom_map f a) = logic_atom_correct A (T \<circ> f) a"
  by (cases a) (simp add: list_all_iff)
lemma logic_atom_correct_mono:
  "logic_atom_correct A T a \<Longrightarrow> (\<And>t. T t \<Longrightarrow> U t) \<Longrightarrow> logic_atom_correct A U a"
  by (cases a) (auto simp: list_all_iff)
lemma logic_runtime_goal_embed[simp]:
  "logic_runtime_goal_correct A (logic_goal_map logic_embed g) = logic_goal_correct A g"
  by (cases g) (auto simp: logic_atom_correct_map o_def split: logic_atom.splits)
lemma logic_runtime_goal_subst:
  assumes images: "\<And>x. logic_tree_arity_correct (logic_symbol_arity A) (s x)"
    and goal: "logic_runtime_goal_correct A g"
  shows "logic_runtime_goal_correct A (logic_goal_map (logic_subst s) g)"
  using goal
  by (cases g) (auto simp: logic_atom_correct_map o_def list_all_iff
    intro: logic_atom_correct_mono logic_subst_arity_correct[OF _ images] split: logic_atom.splits)
lemma logic_runtime_goal_bind:
  "logic_runtime_goal_correct A (logic_bind_cut m f g) =
    logic_runtime_goal_correct A (logic_goal_map f g)"
  by (cases g) auto
lemma logic_runtime_goal_eval:
  assumes images: "\<And>x. logic_tree_arity_correct (logic_symbol_arity A) (s x)"
    and goal: "logic_goal_correct A g"
  shows "logic_runtime_goal_correct A (logic_goal_map (logic_eval s) g)"
proof -
  have maps: "logic_goal_map (logic_eval s) g =
    logic_goal_map (logic_subst s) (logic_goal_map logic_embed g)"
    by (cases g) (simp_all add: logic_atom_map_comp o_def)
  show ?thesis unfolding maps
    by (rule logic_runtime_goal_subst[OF images]) (simp add: goal)
qed

lemma logic_runtime_prune_correct:
  "logic_runtime_state_correct A es \<Longrightarrow> logic_runtime_state_correct A (logic_prune m es)"
  by (induct es) (auto split: logic_choice.splits)
lemma logic_runtime_admin_correct:
  "logic_admin s = Some t \<Longrightarrow> logic_runtime_state_correct A s \<Longrightarrow>
    logic_runtime_state_correct A t"
  by (induct s rule: logic_admin.induct)
    (auto split: logic_goal.splits intro: logic_runtime_prune_correct)
lemma logic_runtime_lower_correct:
  "logic_lower m t gs \<Longrightarrow> logic_tree_arity_correct (logic_symbol_arity A) t \<Longrightarrow>
    list_all (logic_runtime_goal_correct A) gs"
  by (induct rule: logic_lower.induct) auto

lemma logic_cut_step_arity:
  assumes program: "logic_cut_problem A P p modes"
    and step: "logic_cut_step A D P s t"
    and correct: "logic_runtime_state_correct A s"
  shows "logic_runtime_state_correct A t"
  using step correct
proof (cases rule: logic_cut_step.cases)
  case admin
  then show ?thesis using correct by (auto intro: logic_runtime_admin_correct)
next
  case case_call
  then show ?thesis using correct by (auto simp: list_all_iff)
next
  case (resolve c ren a gs sigma m es)
  have images: "logic_tree_arity_correct (logic_symbol_arity A) (sigma x)" for x
    using resolve unfolding logic_mgu_def logic_substitution_in_def by blast
  have body: "list_all (logic_goal_correct A) (snd (P!c))"
    using program nth_mem[OF resolve(3)]
    by (auto simp: logic_cut_problem_def case_prod_unfold)
  have clause: "logic_runtime_goal_correct A
      (logic_bind_cut m (logic_subst sigma \<circ> logic_eval (LVar \<circ> ren)) g)"
    if "logic_goal_correct A g" for g
  proof -
    have eq: "(logic_subst sigma \<circ> logic_eval (LVar \<circ> ren)) = logic_eval (sigma \<circ> ren)"
      by (rule ext) (simp add: logic_subst_composition o_def)
    show ?thesis unfolding eq logic_runtime_goal_bind
      by (rule logic_runtime_goal_eval[OF _ that]) (simp add: images)
  qed
  show ?thesis using resolve body correct
    by (auto simp: list_all_iff intro: clause logic_runtime_goal_subst[OF images])
next
  case backtrack
  then show ?thesis using correct by simp
next
  case (unify a b sigma gs es)
  have images: "logic_tree_arity_correct (logic_symbol_arity A) (sigma x)" for x
    using unify unfolding logic_mgu_def logic_substitution_in_def by blast
  show ?thesis using unify correct
    by (auto simp: list_all_iff intro: logic_runtime_goal_subst[OF images])
next
  case unify_fail
  then show ?thesis using correct by simp
next
  case (meta m f ts gs es body)
  then show ?thesis using correct by (auto intro: logic_runtime_lower_correct)
next
  case meta_diverges
  then show ?thesis using correct by simp
qed

lemma logic_cut_run_arity:
  assumes "logic_cut_problem A P p modes" "logic_runtime_state_correct A (run 0)"
    "\<And>n. logic_cut_step A D P (run n) (run (Suc n))"
  shows "logic_runtime_state_correct A (run n)"
  by (induct n) (use assms in \<open>auto intro: logic_cut_step_arity\<close>)

end
