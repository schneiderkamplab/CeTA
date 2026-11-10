theory LP_Cut_Execution_Properties
  imports LP_Properties
begin

text \<open>Renaming invocation marks does not rename term variables. These
execution lemmas are shared by all term domains and keep administrative
invariants outside the human-facing definitions.\<close>
fun logic_scope_goal where
  "logic_scope_goal r (LogicCut m) = LogicCut (r m)"
| "logic_scope_goal r g = g"
fun logic_scope_choice where
  "logic_scope_choice r (LogicGoals gs) = LogicGoals (map (logic_scope_goal r) gs)"
| "logic_scope_choice r (LogicClause gs c m) = LogicClause (map (logic_scope_goal r) gs) c (r m)"
| "logic_scope_choice r (LogicBarrier m) = LogicBarrier (r m)"
lemma logic_scope_terms[simp]:
  "logic_goal_terms (logic_scope_goal r g) = logic_goal_terms g"
  by (cases g) auto
lemma logic_scope_goal_map:
  "logic_scope_goal r (logic_goal_map f g) = logic_goal_map f (logic_scope_goal r g)"
  by (cases g) auto
lemma logic_scope_bind:
  "logic_scope_goal r (logic_bind_cut m f g) = logic_bind_cut (r m) f g"
  by (cases g) auto
lemma logic_scope_goal_marks:
  "logic_goal_marks (logic_scope_goal r g) = r ` logic_goal_marks g"
  by (cases g) auto
lemma logic_scope_choice_marks:
  "logic_choice_marks (logic_scope_choice r e) = r ` logic_choice_marks e"
  by (cases e) (auto simp: logic_scope_goal_marks image_image)
lemma logic_scope_fresh:
  "inj r \<Longrightarrow> logic_fresh_mark m es \<Longrightarrow>
    logic_fresh_mark (r m) (map (logic_scope_choice r) es)"
  by (auto simp: logic_fresh_mark_def logic_scope_choice_marks image_image dest: injD)
lemma logic_scope_prune:
  "inj r \<Longrightarrow> map (logic_scope_choice r) (logic_prune m es) =
    logic_prune (r m) (map (logic_scope_choice r) es)"
  by (induct es) (auto split: logic_choice.splits simp: inj_eq)
lemma logic_scope_admin:
  assumes "inj r" "logic_admin s = Some t"
  shows "logic_admin (map (logic_scope_choice r) s) = Some (map (logic_scope_choice r) t)"
  using assms by (induct s rule: logic_admin.induct)
    (auto simp: logic_scope_prune split: logic_goal.splits)
lemma logic_scope_lower:
  "logic_lower m a gs \<Longrightarrow> logic_lower (r m) a (map (logic_scope_goal r) gs)"
  by (induct rule: logic_lower.induct) (auto intro: logic_lower.intros)
lemma logic_scope_resolve_mgu:
  "logic_cut_mgu D a gs h bs s t \<Longrightarrow>
    logic_cut_mgu D a (map (logic_scope_goal r) gs) h bs s t"
  by (simp add: logic_cut_mgu_def map_map o_def)
lemma logic_scope_unify_mgu:
  assumes "logic_unify_mgu D a b gs s"
  shows "logic_unify_mgu D a b (map (logic_scope_goal r) gs) s"
proof -
  have mapped: "map (logic_goal_map f) (map (logic_scope_goal r) gs) =
    map (logic_scope_goal r) (map (logic_goal_map f) gs)" for f
    by (simp add: map_map o_def logic_scope_goal_map)
  have factor: "\<exists>d. logic_substitution D d \<and>
      logic_subst d (logic_subst s a) = logic_subst u a \<and>
      map (logic_goal_map (logic_subst d \<circ> logic_subst s)) (map (logic_scope_goal r) gs) =
      map (logic_goal_map (logic_subst u)) (map (logic_scope_goal r) gs)"
    if domain: "logic_substitution D u" and equation: "logic_subst u a = logic_subst u b" for u
  proof -
    obtain d where dom: "logic_substitution D d"
      and atom: "logic_subst d (logic_subst s a) = logic_subst u a"
      and goals: "map (logic_goal_map (logic_subst d \<circ> logic_subst s)) gs =
        map (logic_goal_map (logic_subst u)) gs"
      using assms domain equation unfolding logic_unify_mgu_def by blast
    show ?thesis
      by (rule exI[of _ d], rule conjI[OF dom], rule conjI[OF atom])
        (simp only: mapped goals)
  qed
  show ?thesis using assms factor unfolding logic_unify_mgu_def by blast
qed

lemma logic_cut_step_scopes:
  assumes step: "logic_cut_step D P s t" and injective: "inj r"
  shows "logic_cut_step D P (map (logic_scope_choice r) s) (map (logic_scope_choice r) t)"
  using step
proof (cases rule: logic_cut_step.cases)
  case admin
  then show ?thesis by (auto intro: logic_cut_step.admin logic_scope_admin[OF injective])
next
  case (case_call m f ts gs es)
  have fresh: "logic_fresh_mark (r m)
    (map (logic_scope_choice r) (LogicGoals (LogicAtom (LFun (LogicUser f) ts)#gs)#es))"
    by (rule logic_scope_fresh[OF injective]) (use case_call in blast)
  show ?thesis using logic_cut_step.case_call[OF fresh[simplified], where D=D and P=P] case_call
    by (simp add: map_map o_def)
next
  case (resolve c a gs sigma rho m es)
  have mgu: "logic_cut_mgu D a (map (logic_scope_goal r) gs) (fst (P!c)) (snd (P!c)) sigma rho"
    by (rule logic_scope_resolve_mgu) (use resolve in blast)
  show ?thesis using logic_cut_step.resolve[OF _ mgu, where m="r m" and es="map (logic_scope_choice r) es"] resolve
    by (simp add: map_map o_def logic_scope_bind logic_scope_goal_map)
next
  case (backtrack c a gs m)
  then show ?thesis by (auto intro: logic_cut_step.backtrack)
next
  case (unify a b gs sigma es)
  have mgu: "logic_unify_mgu D a b (map (logic_scope_goal r) gs) sigma"
    by (rule logic_scope_unify_mgu) (use unify in blast)
  show ?thesis using logic_cut_step.unify[OF mgu, where es="map (logic_scope_choice r) es"] unify
    by (simp add: map_map o_def logic_scope_goal_map)
next
  case (unify_fail a b gs)
  then show ?thesis by (auto intro: logic_cut_step.unify_fail)
next
  case (meta m f ts gs es body)
  have fresh: "logic_fresh_mark (r m)
    (map (logic_scope_choice r) (LogicGoals (LogicMeta (LFun f ts)#gs)#es))"
    by (rule logic_scope_fresh[OF injective]) (use meta in blast)
  have lower: "logic_lower (r m) (LFun f ts) (map (logic_scope_goal r) body)"
    by (rule logic_scope_lower) (use meta in blast)
  show ?thesis using logic_cut_step.meta[OF fresh[simplified] lower, where D=D and P=P] meta by simp
next
  case (meta_diverges a gs es)
  then show ?thesis by (auto intro: logic_cut_step.meta_diverges)
qed

end
