theory Higher_Order_Application
  imports Higher_Order_Expansion
begin

definition ho_application_rule where
  "ho_application_rule A B c =
    ([HArrow A B,A],
     PApp (PApp (PConst c) (PMeta 0 [])) (PMeta 1 []),
     PApp (PMeta 0 []) (PMeta 1 []))"

definition ho_application_interpretation where
  "ho_application_interpretation A B c n = (if n=c then
     HAbs (HArrow A B) (HAbs A (HApp (HBound 1) (HBound 0))) else HConst n)"

lemma ho_lift_0: "ho_lift 0 k t=t"
  by (induction t arbitrary: k) auto

lemma ho_beta_plus_left:
  "beta\<^sup>+\<^sup>+ s t \<Longrightarrow> beta\<^sup>+\<^sup>+ (App s x) (App t x)"
  by (induction rule: tranclp_induct) (auto intro: tranclp.intros)

lemma ho_beta_plus_right:
  "beta\<^sup>+\<^sup>+ s t \<Longrightarrow> beta\<^sup>+\<^sup>+ (App x s) (App x t)"
  by (induction rule: tranclp_induct) (auto intro: tranclp.intros)

lemma ho_beta_plus_abs:
  "beta\<^sup>+\<^sup>+ s t \<Longrightarrow> beta\<^sup>+\<^sup>+ (Abs s) (Abs t)"
  by (induction rule: tranclp_induct) (auto intro: tranclp.intros)

lemma ho_application_beta:
  "beta\<^sup>+\<^sup>+ (App (App (Abs (Abs (App (Var 1) (Var 0)))) f) x) (App f x)"
proof -
  have first: "beta (App (App (Abs (Abs (App (Var 1) (Var 0)))) f) x)
      (App (Abs (App (lift f 0) (Var 0))) x)"
    using beta.beta[of "Abs (App (Var 1) (Var 0))" f]
    by (auto simp: subst_Var intro: beta.appL)
  have second: "beta (App (Abs (App (lift f 0) (Var 0))) x) (App f x)"
    using beta.beta[of "App (lift f 0) (Var 0)" x] by simp
  show ?thesis using first second by (meson tranclp.r_into_trancl tranclp.trancl_into_trancl)
qed

lemma ho_application_step_simulation:
  assumes step: "ho_step S V [ho_application_rule A B c] G t u"
  shows "beta\<^sup>+\<^sup>+ (ho_db d (ho_expand (ho_application_interpretation A B c) t))
    (ho_db d (ho_expand (ho_application_interpretation A B c) u))"
  using step
proof (induction arbitrary: d rule: ho_step.induct)
  case (rule G l r H s t u)
  then show ?case
    by (auto simp: ho_application_rule_def ho_application_interpretation_def ho_lift_0
       intro: ho_application_beta[simplified])
next
  case (beta H T t u)
  have closed: "\<And>n. ho_closed_at 0 (ho_application_interpretation A B c n)"
    by (simp add: ho_application_interpretation_def)
  have "ho_step S V [] H
    (ho_expand (ho_application_interpretation A B c) (HApp (HAbs T t) u))
    (ho_expand (ho_application_interpretation A B c) (ho_beta_subst u 0 t))"
    by (rule ho_expand_beta_step[OF closed ho_step.beta])
  then show ?case by (intro tranclp.r_into_trancl) (rule ho_db_beta_step)
qed (auto intro: ho_beta_plus_left ho_beta_plus_right ho_beta_plus_abs)

theorem ho_application_termination:
  assumes c: "c<length S" "S!c = HArrow (HArrow A B) (HArrow A B)"
  shows "wf ((ho_relation S V [ho_application_rule A B c] T)\<inverse>)"
proof (rule ho_beta_simulation_termination[where I="ho_application_interpretation A B c"])
  show "ho_closed_at 0 (ho_application_interpretation A B c n)" for n
    by (simp add: ho_application_interpretation_def)
  show "ho_typeof S [] [] (ho_application_interpretation A B c n) = Some (S!n)"
    if "n<length S" for n
    using that c by (simp add: ho_application_interpretation_def)
  show "beta\<^sup>+\<^sup>+ (ho_db 0 (ho_expand (ho_application_interpretation A B c) t))
       (ho_db 0 (ho_expand (ho_application_interpretation A B c) u))"
    if "ho_step S V [ho_application_rule A B c] [] t u" for t u
    by (rule ho_application_step_simulation[OF that])
qed

definition ho_check_application where
  "ho_check_application S R c \<longleftrightarrow> c<length S \<and>
    (case S!c of HArrow (HArrow A B) (HArrow C D) \<Rightarrow>
      A=C \<and> B=D \<and> R=[ho_application_rule A B c] | _ \<Rightarrow> False)"

theorem ho_check_application_sound:
  "ho_check_application S R c \<Longrightarrow> wf ((ho_relation S V R T)\<inverse>)"
  unfolding ho_check_application_def
  by (auto split: ho_type.splits intro: ho_application_termination)

end
