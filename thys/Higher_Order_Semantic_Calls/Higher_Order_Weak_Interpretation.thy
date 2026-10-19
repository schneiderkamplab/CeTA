theory Higher_Order_Weak_Interpretation
  imports "Higher_Order_Polynomial.Higher_Order_Polynomial_Checker"
begin

definition ho_plain_app where
  "ho_plain_app A B f x=App f x"

lemma ho_plain_app_subst:
  "(ho_plain_app A B f x)[v/k]=ho_plain_app A B (f[v/k]) (x[v/k])"
  by (simp add: ho_plain_app_def)

lemma ho_plain_app_lift:
  "lift (ho_plain_app A B f x) k=ho_plain_app A B (lift f k) (lift x k)"
  by (simp add: ho_plain_app_def)

lemma ho_plain_app_value:
  "ho_value (HArrow A B) f \<Longrightarrow> ho_value A x \<Longrightarrow> ho_value B (ho_plain_app A B f x)"
  by (simp add: ho_plain_app_def)

lemma ho_plain_app_ge:
  assumes f: "ho_value (HArrow A B) f" and g: "ho_value (HArrow A B) g"
    and x: "ho_value A x" and y: "ho_value A y"
    and fg: "ho_value_ge (HArrow A B) f g" and xy: "ho_value_ge A x y"
  shows "ho_value_ge B (ho_plain_app A B f x) (ho_plain_app A B g y)"
proof -
  have left: "ho_value_ge B (App f x) (App g x)" using fg x by simp
  have right: "ho_value_ge B (App g x) (App g y)" using g x y xy by simp
  show ?thesis unfolding ho_plain_app_def by (rule ho_value_ge_trans[OF left right])
qed

lemma ho_plain_app_dominates:
  "ho_value (HArrow A B) f \<Longrightarrow> ho_value A x \<Longrightarrow>
    ho_value_ge B (ho_plain_app A B f x) (App f x)"
  by (simp add: ho_plain_app_def ho_value_ge_refl)

fun ho_weak_evaluate where
  "ho_weak_evaluate I e (HEVar n) = e n"
| "ho_weak_evaluate I e (HEConst n) = I n"
| "ho_weak_evaluate I e (HEApp A B f x) =
    ho_plain_app A B (ho_weak_evaluate I e f) (ho_weak_evaluate I e x)"
| "ho_weak_evaluate I e (HEAbs A B t) = Abs (ho_weak_evaluate I (ho_env_lift e) t)"

lemma ho_weak_evaluate_subst:
  "ho_interpretation_closed I \<Longrightarrow>
    (ho_weak_evaluate I e t)[v/k] = ho_weak_evaluate I (\<lambda>n. (e n)[v/k]) t"
proof (induction t arbitrary: e v k)
  case (HEVar n)
  then show ?case by simp
next
  case (HEConst n)
  then show ?case by (simp add: ho_interpretation_closed_def)
next
  case (HEApp A B f x)
  then show ?case by (simp add: ho_plain_app_subst)
next
  case (HEAbs A B t)
  then show ?case by (simp add: ho_env_lift_subst)
qed

lemma ho_weak_evaluate_abstraction_beta:
  assumes "ho_interpretation_closed I"
  shows "beta (App (ho_weak_evaluate I e (HEAbs A B t)) x)
    (ho_weak_evaluate I (ho_env_cons x e) t)"
  using beta.beta[of "ho_weak_evaluate I (ho_env_lift e) t" x]
  by (simp add: ho_weak_evaluate_subst[OF assms] ho_env_lift_beta)

theorem ho_weak_evaluate_fundamental:
  assumes typing: "ho_expression_type S G t A"
    and closed: "ho_interpretation_closed I"
    and const_values: "ho_env_value S I"
  shows "(\<forall>e. ho_env_value G e \<longrightarrow> ho_value A (ho_weak_evaluate I e t)) \<and>
    (\<forall>e d. ho_env_value G e \<longrightarrow> ho_env_value G d \<longrightarrow> ho_env_ge G e d \<longrightarrow>
      ho_value_ge A (ho_weak_evaluate I e t) (ho_weak_evaluate I d t))"
using typing
proof induction
  case (var n G)
  then show ?case by (auto simp: ho_env_value_def ho_env_ge_def)
next
  case (const n G)
  have cv: "ho_value (S!n) (I n)" using const_values const.hyps by (simp add: ho_env_value_def)
  show ?case using cv ho_value_ge_refl[OF cv] by simp
next
  case (app G f A B x)
  note fv = app.IH(1)[THEN conjunct1, rule_format]
  note fg = app.IH(1)[THEN conjunct2, rule_format]
  note xv = app.IH(2)[THEN conjunct1, rule_format]
  note xg = app.IH(2)[THEN conjunct2, rule_format]
  have ev: "ho_value B (ho_weak_evaluate I e (HEApp A B f x))"
    if "ho_env_value G e" for e
    unfolding ho_weak_evaluate.simps by (rule ho_plain_app_value[OF fv[OF that] xv[OF that]])
  have order: "ho_value_ge B (ho_weak_evaluate I e (HEApp A B f x)) (ho_weak_evaluate I d (HEApp A B f x))"
    if "ho_env_value G e" "ho_env_value G d" "ho_env_ge G e d" for e d
    unfolding ho_weak_evaluate.simps
    by (rule ho_plain_app_ge[OF fv[OF that(1)] fv[OF that(2)] xv[OF that(1)] xv[OF that(2)]
      fg[OF that] xg[OF that]])
  show ?case using ev order by blast
next
  case (abs A G t B)
  note ev = abs.IH[THEN conjunct1, rule_format]
  note order = abs.IH[THEN conjunct2, rule_format]
  have path: "beta\<^sup>*\<^sup>* (App (ho_weak_evaluate I e (HEAbs A B t)) x)
      (ho_weak_evaluate I (ho_env_cons x e) t)" for e x
    by (rule r_into_rtranclp) (rule ho_weak_evaluate_abstraction_beta[OF closed])
  have appvalue: "ho_value B (App (ho_weak_evaluate I e (HEAbs A B t)) x)"
    if e: "ho_env_value G e" and x: "ho_value A x" for e x
  proof -
    have v: "ho_value B (ho_weak_evaluate I (ho_env_cons x e) t)"
      by (rule ev[OF ho_env_cons_value[OF x e]])
    have eq: "ho_value B (App (ho_weak_evaluate I e (HEAbs A B t)) x) =
        ho_value B (ho_weak_evaluate I (ho_env_cons x e) t)" by (rule ho_value_beta[OF path])
    show ?thesis using v eq by simp
  qed
  have apporder: "ho_value_ge B (App (ho_weak_evaluate I e (HEAbs A B t)) x)
      (App (ho_weak_evaluate I d (HEAbs A B t)) y)"
    if e: "ho_env_value G e" and d: "ho_env_value G d" and ed: "ho_env_ge G e d"
      and x: "ho_value A x" and y: "ho_value A y" and xy: "ho_value_ge A x y" for e d x y
  proof -
    have g: "ho_value_ge B (ho_weak_evaluate I (ho_env_cons x e) t) (ho_weak_evaluate I (ho_env_cons y d) t)"
      by (rule order[OF ho_env_cons_value[OF x e] ho_env_cons_value[OF y d] ho_env_cons_ge[OF xy ed]])
    have eq: "ho_value_ge B (App (ho_weak_evaluate I e (HEAbs A B t)) x)
        (App (ho_weak_evaluate I d (HEAbs A B t)) y) =
      ho_value_ge B (ho_weak_evaluate I (ho_env_cons x e) t) (ho_weak_evaluate I (ho_env_cons y d) t)"
      by (rule ho_ge_beta[OF path path])
    show ?thesis using g eq by simp
  qed
  have val: "ho_value (HArrow A B) (ho_weak_evaluate I e (HEAbs A B t))"
    if e: "ho_env_value G e" for e
    unfolding ho_value.simps(2)
    using appvalue[OF e] apporder[OF e e ho_env_ge_refl[OF e]] by blast
  have ge: "ho_value_ge (HArrow A B) (ho_weak_evaluate I e (HEAbs A B t))
      (ho_weak_evaluate I d (HEAbs A B t))"
    if "ho_env_value G e" "ho_env_value G d" "ho_env_ge G e d" for e d
    unfolding ho_value_ge.simps(2)
    using apporder[OF that] ho_value_ge_refl by blast
  show ?case using val ge by blast
qed

lemma ho_weak_evaluate_lift:
  "ho_interpretation_closed I \<Longrightarrow>
    lift (ho_weak_evaluate I e t) k = ho_weak_evaluate I (\<lambda>n. lift (e n) k) t"
proof (induction t arbitrary: e k)
  case (HEVar n)
  then show ?case by simp
next
  case (HEConst n)
  then show ?case by (simp add: ho_interpretation_closed_def)
next
  case (HEApp A B f x)
  then show ?case by (simp add: ho_plain_app_lift)
next
  case (HEAbs A B t)
  then show ?case by (simp add: ho_env_lift_lift)
qed

lemma ho_weak_evaluate_rename:
  "ho_weak_evaluate I e (ho_expr_rename r t) = ho_weak_evaluate I (\<lambda>n. e (r n)) t"
  by (induction t arbitrary: e r) (simp_all add: ho_env_lift_rename)

lemma ho_weak_evaluate_subst_up:
  assumes "ho_interpretation_closed I"
  shows "ho_weak_evaluate I (ho_env_lift e) (ho_expr_subst_up s n) =
    ho_env_lift (\<lambda>i. ho_weak_evaluate I e (s i)) n"
  by (cases n) (simp_all add: ho_expr_subst_up_def ho_weak_evaluate_rename
    ho_env_lift_def ho_env_cons_def ho_weak_evaluate_lift[OF assms])

lemma ho_weak_evaluate_expr_subst:
  "ho_interpretation_closed I \<Longrightarrow>
    ho_weak_evaluate I e (ho_expr_subst s t) = ho_weak_evaluate I (\<lambda>n. ho_weak_evaluate I e (s n)) t"
  by (induction t arbitrary: e s) (simp_all add: ho_weak_evaluate_subst_up)

lemma ho_weak_evaluate_beta_subst:
  assumes closed: "ho_interpretation_closed I"
  shows "ho_weak_evaluate I e (ho_expr_beta_subst x t) =
    ho_weak_evaluate I (ho_env_cons (ho_weak_evaluate I e x) e) t"
proof -
  have env: "(\<lambda>n. ho_weak_evaluate I e (case n of 0 \<Rightarrow> x | Suc k \<Rightarrow> HEVar k)) =
      ho_env_cons (ho_weak_evaluate I e x) e"
  proof (rule ext)
    fix n
    show "ho_weak_evaluate I e (case n of 0 \<Rightarrow> x | Suc k \<Rightarrow> HEVar k) =
        ho_env_cons (ho_weak_evaluate I e x) e n"
      by (cases n) (simp_all add: ho_env_cons_def)
  qed
  show ?thesis by (simp add: ho_expr_beta_subst_def ho_weak_evaluate_expr_subst[OF closed] env)
qed

theorem ho_weak_evaluate_beta_weak:
  assumes body: "ho_expression_type S (A#G) t B" and arg: "ho_expression_type S G x A"
    and closed: "ho_interpretation_closed I" and const_values: "ho_env_value S I"
    and env: "ho_env_value G e"
  shows "ho_value_ge B (ho_weak_evaluate I e (HEApp A B (HEAbs A B t) x))
    (ho_weak_evaluate I e (ho_expr_beta_subst x t))"
proof -
  have fun_type: "ho_expression_type S G (HEAbs A B t) (HArrow A B)"
    by (rule ho_expression_type.abs[OF body])
  have fv: "ho_value (HArrow A B) (ho_weak_evaluate I e (HEAbs A B t))"
    by (rule ho_weak_evaluate_fundamental[OF fun_type closed const_values, THEN conjunct1, rule_format, OF env])
  have xv: "ho_value A (ho_weak_evaluate I e x)"
    by (rule ho_weak_evaluate_fundamental[OF arg closed const_values, THEN conjunct1, rule_format, OF env])
  have weak: "ho_value_ge B (ho_weak_evaluate I e (HEApp A B (HEAbs A B t) x))
      (App (ho_weak_evaluate I e (HEAbs A B t)) (ho_weak_evaluate I e x))"
    unfolding ho_weak_evaluate.simps(3) by (rule ho_plain_app_dominates[OF fv xv])
  have path: "beta\<^sup>*\<^sup>* (App (ho_weak_evaluate I e (HEAbs A B t)) (ho_weak_evaluate I e x))
      (ho_weak_evaluate I e (ho_expr_beta_subst x t))"
    unfolding ho_weak_evaluate_beta_subst[OF closed]
    by (rule r_into_rtranclp) (rule ho_weak_evaluate_abstraction_beta[OF closed])
  have eq: "ho_value_ge B (ho_weak_evaluate I e (HEApp A B (HEAbs A B t) x))
        (App (ho_weak_evaluate I e (HEAbs A B t)) (ho_weak_evaluate I e x)) =
      ho_value_ge B (ho_weak_evaluate I e (HEApp A B (HEAbs A B t) x))
        (ho_weak_evaluate I e (ho_expr_beta_subst x t))"
    by (rule ho_ge_beta[OF rtranclp.rtrancl_refl path])
  show ?thesis using weak eq by simp
qed

lemma ho_weak_evaluate_instance_ge:
  assumes closed: "ho_interpretation_closed I" and cv: "ho_env_value S I"
    and ev: "ho_env_value D e"
    and subst: "\<And>n. n<length G \<Longrightarrow> ho_expression_type S D (s n) (G!n)"
    and orient: "\<And>d. ho_env_value G d \<Longrightarrow>
      ho_value_ge A (ho_weak_evaluate I d l) (ho_weak_evaluate I d r)"
  shows "ho_value_ge A (ho_weak_evaluate I e (ho_expr_subst s l)) (ho_weak_evaluate I e (ho_expr_subst s r))"
proof -
  have mapped: "ho_env_value G (\<lambda>n. ho_weak_evaluate I e (s n))"
    unfolding ho_env_value_def
  proof (intro allI impI)
    fix n assume n: "n<length G"
    show "ho_value (G!n) (ho_weak_evaluate I e (s n))"
      by (rule ho_weak_evaluate_fundamental[OF subst[OF n] closed cv, THEN conjunct1, rule_format, OF ev])
  qed
  show ?thesis unfolding ho_weak_evaluate_expr_subst[OF closed] by (rule orient[OF mapped])
qed

lemma ho_weak_evaluate_instance_gt:
  assumes closed: "ho_interpretation_closed I" and cv: "ho_env_value S I"
    and ev: "ho_env_value D e"
    and subst: "\<And>n. n<length G \<Longrightarrow> ho_expression_type S D (s n) (G!n)"
    and orient: "\<And>d. ho_env_value G d \<Longrightarrow>
      ho_value_gt A (ho_weak_evaluate I d l) (ho_weak_evaluate I d r)"
  shows "ho_value_gt A (ho_weak_evaluate I e (ho_expr_subst s l)) (ho_weak_evaluate I e (ho_expr_subst s r))"
proof -
  have mapped: "ho_env_value G (\<lambda>n. ho_weak_evaluate I e (s n))"
    unfolding ho_env_value_def
  proof (intro allI impI)
    fix n assume n: "n<length G"
    show "ho_value (G!n) (ho_weak_evaluate I e (s n))"
      by (rule ho_weak_evaluate_fundamental[OF subst[OF n] closed cv, THEN conjunct1, rule_format, OF ev])
  qed
  show ?thesis unfolding ho_weak_evaluate_expr_subst[OF closed] by (rule orient[OF mapped])
qed

end
