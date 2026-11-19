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
lemma logic_cut_step_scopes:
  assumes step: "logic_cut_step A D P s t" and injective: "inj r"
  shows "logic_cut_step A D P (map (logic_scope_choice r) s) (map (logic_scope_choice r) t)"
  using step
proof (cases rule: logic_cut_step.cases)
  case admin
  then show ?thesis by (auto intro: logic_cut_step.admin logic_scope_admin[OF injective])
next
  case (case_call m f ts gs es)
  have fresh: "logic_fresh_mark (r m)
    (map (logic_scope_choice r) (LogicGoals (LogicAtom (LAtom f ts)#gs)#es))"
    by (rule logic_scope_fresh[OF injective]) (use case_call in blast)
  show ?thesis using logic_cut_step.case_call[OF fresh[simplified], where A=A and D=D and P=P] case_call
    by (simp add: map_map o_def)
next
  case (resolve c ren a gs sigma m es)
  have fresh: "logic_freshening ren
      (logic_arguments a @ concat (map logic_goal_terms (map (logic_scope_goal r) gs)))
      (logic_arguments (fst (P!c)) @ concat (map logic_goal_terms (snd (P!c))))"
    using resolve by (simp add: map_map o_def)
  show ?thesis using logic_cut_step.resolve[OF _ fresh, where m="r m"
      and es="map (logic_scope_choice r) es" and s=sigma and A=A and D=D] resolve
    by (simp add: map_map o_def logic_scope_bind logic_scope_goal_map)
next
  case (backtrack c ren a gs m)
  then show ?thesis
    by (auto simp: map_map o_def intro: logic_cut_step.backtrack)
next
  case (unify a b sigma gs es)
  show ?thesis using logic_cut_step.unify[where es="map (logic_scope_choice r) es"
      and gs="map (logic_scope_goal r) gs" and A=A and D=D and P=P] unify
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
  show ?thesis using logic_cut_step.meta[OF fresh[simplified] lower, where A=A and D=D and P=P] meta by simp
next
  case (meta_diverges a gs es)
  then show ?thesis by (auto intro: logic_cut_step.meta_diverges)
qed

end
