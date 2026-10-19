theory Higher_Order_Interpretation
  imports Higher_Order_Semantic_Application
begin

datatype ho_expression = HEVar nat | HEConst nat
  | HEApp ho_type ho_type ho_expression ho_expression
  | HEAbs ho_type ho_type ho_expression

inductive ho_expression_type :: "ho_type list \<Rightarrow> ho_type list \<Rightarrow>
    ho_expression \<Rightarrow> ho_type \<Rightarrow> bool" for S where
  var: "n<length G \<Longrightarrow> ho_expression_type S G (HEVar n) (G!n)"
| const: "n<length S \<Longrightarrow> ho_expression_type S G (HEConst n) (S!n)"
| app: "ho_expression_type S G f (HArrow A B) \<Longrightarrow>
    ho_expression_type S G x A \<Longrightarrow> ho_expression_type S G (HEApp A B f x) B"
| abs: "ho_expression_type S (A#G) t B \<Longrightarrow>
    ho_expression_type S G (HEAbs A B t) (HArrow A B)"

definition ho_env_cons where
  "ho_env_cons x e n = (case n of 0 \<Rightarrow> x | Suc k \<Rightarrow> e k)"

definition ho_env_lift where
  "ho_env_lift e = ho_env_cons (Var 0) (\<lambda>n. lift (e n) 0)"

fun ho_evaluate where
  "ho_evaluate I e (HEVar n) = e n"
| "ho_evaluate I e (HEConst n) = I n"
| "ho_evaluate I e (HEApp A B f x) =
    ho_sem_app A B (ho_evaluate I e f) (ho_evaluate I e x)"
| "ho_evaluate I e (HEAbs A B t) = Abs (ho_evaluate I (ho_env_lift e) t)"

definition ho_interpretation_closed where
  "ho_interpretation_closed I \<longleftrightarrow>
    (\<forall>n v k. (I n)[v/k]=I n) \<and> (\<forall>n k. lift (I n) k=I n)"

lemma ho_env_lift_subst:
  "(ho_env_lift e n)[lift v 0/Suc k] = ho_env_lift (\<lambda>i. (e i)[v/k]) n"
  by (cases n) (simp_all add: ho_env_lift_def ho_env_cons_def)

lemma ho_evaluate_subst:
  "ho_interpretation_closed I \<Longrightarrow>
    (ho_evaluate I e t)[v/k] = ho_evaluate I (\<lambda>n. (e n)[v/k]) t"
proof (induction t arbitrary: e v k)
  case (HEVar n)
  then show ?case by simp
next
  case (HEConst n)
  then show ?case by (simp add: ho_interpretation_closed_def)
next
  case (HEApp A B f x)
  then show ?case by (simp add: ho_sem_app_subst)
next
  case (HEAbs A B t)
  then show ?case by (simp add: ho_env_lift_subst)
qed

lemma ho_env_lift_beta:
  "(\<lambda>n. (ho_env_lift e n)[x/0]) = ho_env_cons x e"
proof (rule ext)
  fix n
  show "(ho_env_lift e n)[x/0] = ho_env_cons x e n"
    by (cases n) (simp_all add: ho_env_lift_def ho_env_cons_def)
qed

lemma ho_evaluate_abstraction_beta:
  assumes "ho_interpretation_closed I"
  shows "beta (App (ho_evaluate I e (HEAbs A B t)) x)
    (ho_evaluate I (ho_env_cons x e) t)"
  using beta.beta[of "ho_evaluate I (ho_env_lift e) t" x]
  by (simp add: ho_evaluate_subst[OF assms] ho_env_lift_beta)

definition ho_env_value where
  "ho_env_value G e \<longleftrightarrow> (\<forall>n<length G. ho_value (G!n) (e n))"

definition ho_env_ge where
  "ho_env_ge G e d \<longleftrightarrow> (\<forall>n<length G. ho_value_ge (G!n) (e n) (d n))"

lemma ho_env_cons_value:
  "ho_value A x \<Longrightarrow> ho_env_value G e \<Longrightarrow> ho_env_value (A#G) (ho_env_cons x e)"
  unfolding ho_env_value_def ho_env_cons_def by (auto split: nat.splits)

lemma ho_env_cons_ge:
  "ho_value_ge A x y \<Longrightarrow> ho_env_ge G e d \<Longrightarrow>
    ho_env_ge (A#G) (ho_env_cons x e) (ho_env_cons y d)"
  unfolding ho_env_ge_def ho_env_cons_def by (auto split: nat.splits)

lemma ho_env_ge_refl:
  "ho_env_value G e \<Longrightarrow> ho_env_ge G e e"
  unfolding ho_env_value_def ho_env_ge_def by (blast intro: ho_value_ge_refl)

theorem ho_evaluate_fundamental:
  assumes typing: "ho_expression_type S G t A"
    and closed: "ho_interpretation_closed I"
    and const_values: "ho_env_value S I"
  shows "(\<forall>e. ho_env_value G e \<longrightarrow> ho_value A (ho_evaluate I e t)) \<and>
    (\<forall>e d. ho_env_value G e \<longrightarrow> ho_env_value G d \<longrightarrow> ho_env_ge G e d \<longrightarrow>
      ho_value_ge A (ho_evaluate I e t) (ho_evaluate I d t))"
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
  have ev: "ho_value B (ho_evaluate I e (HEApp A B f x))"
    if "ho_env_value G e" for e
    unfolding ho_evaluate.simps by (rule ho_sem_app_value[OF fv[OF that] xv[OF that]])
  have order: "ho_value_ge B (ho_evaluate I e (HEApp A B f x)) (ho_evaluate I d (HEApp A B f x))"
    if "ho_env_value G e" "ho_env_value G d" "ho_env_ge G e d" for e d
    unfolding ho_evaluate.simps
    by (rule ho_sem_app_ge[OF fv[OF that(1)] fv[OF that(2)] xv[OF that(1)] xv[OF that(2)]
      fg[OF that] xg[OF that]])
  show ?case using ev order by blast
next
  case (abs A G t B)
  note ev = abs.IH[THEN conjunct1, rule_format]
  note order = abs.IH[THEN conjunct2, rule_format]
  have path: "beta\<^sup>*\<^sup>* (App (ho_evaluate I e (HEAbs A B t)) x)
      (ho_evaluate I (ho_env_cons x e) t)" for e x
    by (rule r_into_rtranclp) (rule ho_evaluate_abstraction_beta[OF closed])
  have appvalue: "ho_value B (App (ho_evaluate I e (HEAbs A B t)) x)"
    if e: "ho_env_value G e" and x: "ho_value A x" for e x
  proof -
    have v: "ho_value B (ho_evaluate I (ho_env_cons x e) t)"
      by (rule ev[OF ho_env_cons_value[OF x e]])
    have eq: "ho_value B (App (ho_evaluate I e (HEAbs A B t)) x) =
        ho_value B (ho_evaluate I (ho_env_cons x e) t)" by (rule ho_value_beta[OF path])
    show ?thesis using v eq by simp
  qed
  have apporder: "ho_value_ge B (App (ho_evaluate I e (HEAbs A B t)) x)
      (App (ho_evaluate I d (HEAbs A B t)) y)"
    if e: "ho_env_value G e" and d: "ho_env_value G d" and ed: "ho_env_ge G e d"
      and x: "ho_value A x" and y: "ho_value A y" and xy: "ho_value_ge A x y" for e d x y
  proof -
    have g: "ho_value_ge B (ho_evaluate I (ho_env_cons x e) t) (ho_evaluate I (ho_env_cons y d) t)"
      by (rule order[OF ho_env_cons_value[OF x e] ho_env_cons_value[OF y d] ho_env_cons_ge[OF xy ed]])
    have eq: "ho_value_ge B (App (ho_evaluate I e (HEAbs A B t)) x)
        (App (ho_evaluate I d (HEAbs A B t)) y) =
      ho_value_ge B (ho_evaluate I (ho_env_cons x e) t) (ho_evaluate I (ho_env_cons y d) t)"
      by (rule ho_ge_beta[OF path path])
    show ?thesis using g eq by simp
  qed
  have val: "ho_value (HArrow A B) (ho_evaluate I e (HEAbs A B t))"
    if e: "ho_env_value G e" for e
    unfolding ho_value.simps(2)
    using appvalue[OF e] apporder[OF e e ho_env_ge_refl[OF e]] by blast
  have ge: "ho_value_ge (HArrow A B) (ho_evaluate I e (HEAbs A B t))
      (ho_evaluate I d (HEAbs A B t))"
    if "ho_env_value G e" "ho_env_value G d" "ho_env_ge G e d" for e d
    unfolding ho_value_ge.simps(2)
    using apporder[OF that] ho_value_ge_refl by blast
  show ?case using val ge by blast
qed

lemma ho_env_lift_lift:
  "lift (ho_env_lift e n) (Suc k) = ho_env_lift (\<lambda>i. lift (e i) k) n"
  by (cases n) (simp_all add: ho_env_lift_def ho_env_cons_def ho_lift_lift_zero)

lemma ho_evaluate_lift:
  "ho_interpretation_closed I \<Longrightarrow>
    lift (ho_evaluate I e t) k = ho_evaluate I (\<lambda>n. lift (e n) k) t"
proof (induction t arbitrary: e k)
  case (HEVar n)
  then show ?case by simp
next
  case (HEConst n)
  then show ?case by (simp add: ho_interpretation_closed_def)
next
  case (HEApp A B f x)
  then show ?case by (simp add: ho_sem_app_lift)
next
  case (HEAbs A B t)
  then show ?case by (simp add: ho_env_lift_lift)
qed

definition ho_rename_up where
  "ho_rename_up r n = (case n of 0 \<Rightarrow> 0 | Suc k \<Rightarrow> Suc (r k))"

fun ho_expr_rename where
  "ho_expr_rename r (HEVar n) = HEVar (r n)"
| "ho_expr_rename r (HEConst n) = HEConst n"
| "ho_expr_rename r (HEApp A B f x) = HEApp A B (ho_expr_rename r f) (ho_expr_rename r x)"
| "ho_expr_rename r (HEAbs A B t) = HEAbs A B (ho_expr_rename (ho_rename_up r) t)"

lemma ho_env_lift_rename:
  "ho_env_lift e (ho_rename_up r n) = ho_env_lift (\<lambda>i. e (r i)) n"
  by (cases n) (simp_all add: ho_env_lift_def ho_env_cons_def ho_rename_up_def)

lemma ho_evaluate_rename:
  "ho_evaluate I e (ho_expr_rename r t) = ho_evaluate I (\<lambda>n. e (r n)) t"
  by (induction t arbitrary: e r) (simp_all add: ho_env_lift_rename)

definition ho_expr_subst_up where
  "ho_expr_subst_up s n = (case n of 0 \<Rightarrow> HEVar 0 | Suc k \<Rightarrow> ho_expr_rename Suc (s k))"

fun ho_expr_subst where
  "ho_expr_subst s (HEVar n) = s n"
| "ho_expr_subst s (HEConst n) = HEConst n"
| "ho_expr_subst s (HEApp A B f x) = HEApp A B (ho_expr_subst s f) (ho_expr_subst s x)"
| "ho_expr_subst s (HEAbs A B t) = HEAbs A B (ho_expr_subst (ho_expr_subst_up s) t)"

lemma ho_evaluate_subst_up:
  assumes "ho_interpretation_closed I"
  shows "ho_evaluate I (ho_env_lift e) (ho_expr_subst_up s n) =
    ho_env_lift (\<lambda>i. ho_evaluate I e (s i)) n"
  by (cases n) (simp_all add: ho_expr_subst_up_def ho_evaluate_rename
    ho_env_lift_def ho_env_cons_def ho_evaluate_lift[OF assms])

lemma ho_evaluate_expr_subst:
  "ho_interpretation_closed I \<Longrightarrow>
    ho_evaluate I e (ho_expr_subst s t) = ho_evaluate I (\<lambda>n. ho_evaluate I e (s n)) t"
  by (induction t arbitrary: e s) (simp_all add: ho_evaluate_subst_up)

definition ho_expr_beta_subst where
  "ho_expr_beta_subst x t = ho_expr_subst (\<lambda>n. case n of 0 \<Rightarrow> x | Suc k \<Rightarrow> HEVar k) t"

lemma ho_evaluate_beta_subst:
  assumes closed: "ho_interpretation_closed I"
  shows "ho_evaluate I e (ho_expr_beta_subst x t) =
    ho_evaluate I (ho_env_cons (ho_evaluate I e x) e) t"
proof -
  have env: "(\<lambda>n. ho_evaluate I e (case n of 0 \<Rightarrow> x | Suc k \<Rightarrow> HEVar k)) =
      ho_env_cons (ho_evaluate I e x) e"
  proof (rule ext)
    fix n
    show "ho_evaluate I e (case n of 0 \<Rightarrow> x | Suc k \<Rightarrow> HEVar k) =
        ho_env_cons (ho_evaluate I e x) e n"
      by (cases n) (simp_all add: ho_env_cons_def)
  qed
  show ?thesis by (simp add: ho_expr_beta_subst_def ho_evaluate_expr_subst[OF closed] env)
qed

theorem ho_evaluate_beta_weak:
  assumes body: "ho_expression_type S (A#G) t B" and arg: "ho_expression_type S G x A"
    and closed: "ho_interpretation_closed I" and const_values: "ho_env_value S I"
    and env: "ho_env_value G e"
  shows "ho_value_ge B (ho_evaluate I e (HEApp A B (HEAbs A B t) x))
    (ho_evaluate I e (ho_expr_beta_subst x t))"
proof -
  have fun_type: "ho_expression_type S G (HEAbs A B t) (HArrow A B)"
    by (rule ho_expression_type.abs[OF body])
  have fv: "ho_value (HArrow A B) (ho_evaluate I e (HEAbs A B t))"
    by (rule ho_evaluate_fundamental[OF fun_type closed const_values, THEN conjunct1, rule_format, OF env])
  have xv: "ho_value A (ho_evaluate I e x)"
    by (rule ho_evaluate_fundamental[OF arg closed const_values, THEN conjunct1, rule_format, OF env])
  have weak: "ho_value_ge B (ho_evaluate I e (HEApp A B (HEAbs A B t) x))
      (App (ho_evaluate I e (HEAbs A B t)) (ho_evaluate I e x))"
    unfolding ho_evaluate.simps(3) by (rule ho_sem_app_dominates[OF fv xv])
  have path: "beta\<^sup>*\<^sup>* (App (ho_evaluate I e (HEAbs A B t)) (ho_evaluate I e x))
      (ho_evaluate I e (ho_expr_beta_subst x t))"
    unfolding ho_evaluate_beta_subst[OF closed]
    by (rule r_into_rtranclp) (rule ho_evaluate_abstraction_beta[OF closed])
  have eq: "ho_value_ge B (ho_evaluate I e (HEApp A B (HEAbs A B t) x))
        (App (ho_evaluate I e (HEAbs A B t)) (ho_evaluate I e x)) =
      ho_value_ge B (ho_evaluate I e (HEApp A B (HEAbs A B t) x))
        (ho_evaluate I e (ho_expr_beta_subst x t))"
    by (rule ho_ge_beta[OF rtranclp.rtrancl_refl path])
  show ?thesis using weak eq by simp
qed

lemma ho_evaluate_instance_ge:
  assumes closed: "ho_interpretation_closed I" and cv: "ho_env_value S I"
    and ev: "ho_env_value D e"
    and subst: "\<And>n. n<length G \<Longrightarrow> ho_expression_type S D (s n) (G!n)"
    and orient: "\<And>d. ho_env_value G d \<Longrightarrow>
      ho_value_ge A (ho_evaluate I d l) (ho_evaluate I d r)"
  shows "ho_value_ge A (ho_evaluate I e (ho_expr_subst s l)) (ho_evaluate I e (ho_expr_subst s r))"
proof -
  have mapped: "ho_env_value G (\<lambda>n. ho_evaluate I e (s n))"
    unfolding ho_env_value_def
  proof (intro allI impI)
    fix n assume n: "n<length G"
    show "ho_value (G!n) (ho_evaluate I e (s n))"
      by (rule ho_evaluate_fundamental[OF subst[OF n] closed cv, THEN conjunct1, rule_format, OF ev])
  qed
  show ?thesis unfolding ho_evaluate_expr_subst[OF closed] by (rule orient[OF mapped])
qed

lemma ho_evaluate_instance_gt:
  assumes closed: "ho_interpretation_closed I" and cv: "ho_env_value S I"
    and ev: "ho_env_value D e"
    and subst: "\<And>n. n<length G \<Longrightarrow> ho_expression_type S D (s n) (G!n)"
    and orient: "\<And>d. ho_env_value G d \<Longrightarrow>
      ho_value_gt A (ho_evaluate I d l) (ho_evaluate I d r)"
  shows "ho_value_gt A (ho_evaluate I e (ho_expr_subst s l)) (ho_evaluate I e (ho_expr_subst s r))"
proof -
  have mapped: "ho_env_value G (\<lambda>n. ho_evaluate I e (s n))"
    unfolding ho_env_value_def
  proof (intro allI impI)
    fix n assume n: "n<length G"
    show "ho_value (G!n) (ho_evaluate I e (s n))"
      by (rule ho_evaluate_fundamental[OF subst[OF n] closed cv, THEN conjunct1, rule_format, OF ev])
  qed
  show ?thesis unfolding ho_evaluate_expr_subst[OF closed] by (rule orient[OF mapped])
qed

end
