theory Higher_Order_Weak_Source
  imports Higher_Order_Weak_Interpretation
begin

definition ho_weak_source_interpretation where
  "ho_weak_source_interpretation S V B I e t = ho_weak_evaluate I e (ho_compile S V B t)"

theorem ho_weak_source_interpretation_value:
  assumes "ho_typeof S V B t=Some A" "ho_interpretation_closed I"
    "ho_env_value S I" "ho_env_value (B@V) e"
  shows "ho_value A (ho_weak_source_interpretation S V B I e t)"
  unfolding ho_weak_source_interpretation_def
  by (rule ho_weak_evaluate_fundamental[OF ho_compile_type[OF assms(1)] assms(2,3),
    THEN conjunct1, rule_format, OF assms(4)])

lemma ho_weak_source_free_instance_ge:
  assumes l: "ho_typeof S G [] l=Some A" and r: "ho_typeof S G [] r=Some A"
    and subst: "ho_typed_subst S V B G s"
    and closed: "ho_interpretation_closed I" and cv: "ho_env_value S I"
    and ev: "ho_env_value (B@V) e"
    and orient: "\<And>d. ho_env_value G d \<Longrightarrow>
      ho_value_ge A (ho_weak_source_interpretation S G [] I d l) (ho_weak_source_interpretation S G [] I d r)"
  shows "ho_value_ge A (ho_weak_source_interpretation S V B I e (ho_subst s 0 l))
    (ho_weak_source_interpretation S V B I e (ho_subst s 0 r))"
proof -
  have sty: "ho_expression_type S (B@V) (ho_compile S V B (s n)) (G!n)"
    if "n<length G" for n
    by (rule ho_compile_type) (use subst that in \<open>simp add: ho_typed_subst_def\<close>)
  show ?thesis unfolding ho_weak_source_interpretation_def
    ho_compile_free_subst[OF l subst] ho_compile_free_subst[OF r subst]
    by (rule ho_weak_evaluate_instance_ge[OF closed cv ev sty])
       (auto intro: orient[unfolded ho_weak_source_interpretation_def])
qed

lemma ho_weak_source_free_instance_gt:
  assumes l: "ho_typeof S G [] l=Some A" and r: "ho_typeof S G [] r=Some A"
    and subst: "ho_typed_subst S V B G s"
    and closed: "ho_interpretation_closed I" and cv: "ho_env_value S I"
    and ev: "ho_env_value (B@V) e"
    and orient: "\<And>d. ho_env_value G d \<Longrightarrow>
      ho_value_gt A (ho_weak_source_interpretation S G [] I d l) (ho_weak_source_interpretation S G [] I d r)"
  shows "ho_value_gt A (ho_weak_source_interpretation S V B I e (ho_subst s 0 l))
    (ho_weak_source_interpretation S V B I e (ho_subst s 0 r))"
proof -
  have sty: "ho_expression_type S (B@V) (ho_compile S V B (s n)) (G!n)"
    if "n<length G" for n
    by (rule ho_compile_type) (use subst that in \<open>simp add: ho_typed_subst_def\<close>)
  show ?thesis unfolding ho_weak_source_interpretation_def
    ho_compile_free_subst[OF l subst] ho_compile_free_subst[OF r subst]
    by (rule ho_weak_evaluate_instance_gt[OF closed cv ev sty])
       (auto intro: orient[unfolded ho_weak_source_interpretation_def])
qed

lemma ho_weak_source_beta_ge:
  assumes body: "ho_typeof S V (A#B) t=Some C" and arg: "ho_typeof S V B x=Some A"
    and closed: "ho_interpretation_closed I" and cv: "ho_env_value S I"
    and ev: "ho_env_value (B@V) e"
  shows "ho_value_ge C (ho_weak_source_interpretation S V B I e (HApp (HAbs A t) x))
    (ho_weak_source_interpretation S V B I e (ho_beta_subst x 0 t))"
proof -
  have bt: "ho_expression_type S (A#(B@V)) (ho_compile S V (A#B) t) C"
    using ho_compile_type[OF body] by simp
  have order: "ho_value_ge C
      (ho_weak_evaluate I e (HEApp A C (HEAbs A C (ho_compile S V (A#B) t)) (ho_compile S V B x)))
      (ho_weak_evaluate I e (ho_expr_beta_subst (ho_compile S V B x) (ho_compile S V (A#B) t)))"
    by (rule ho_weak_evaluate_beta_weak[OF bt ho_compile_type[OF arg] closed cv ev])
  show ?thesis using order
    by (simp add: ho_weak_source_interpretation_def body ho_compile_beta[OF body arg])
qed

definition ho_weak_rule where
  "ho_weak_rule S I G l r \<longleftrightarrow>
    (\<exists>A. ho_typeof S G [] (ho_erase_pattern l)=Some A \<and>
      ho_typeof S G [] (ho_erase_pattern r)=Some A \<and>
      (\<forall>e. ho_env_value G e \<longrightarrow>
        ho_value_ge A (ho_weak_source_interpretation S G [] I e (ho_erase_pattern l))
          (ho_weak_source_interpretation S G [] I e (ho_erase_pattern r))))"

lemma ho_weak_source_rule_ge:
  assumes member: "(G,l,r)\<in>set R" and zero: "ho_zero_arity_rules R"
    and subst: "ho_typed_subst S V B G s"
    and lhs: "ho_instantiate s 0 l=Some t" and rhs: "ho_instantiate s 0 r=Some u"
    and ty: "ho_typeof S V B t=Some A" and orient: "ho_weak_rule S I G l r"
    and closed: "ho_interpretation_closed I" and cv: "ho_env_value S I"
    and ev: "ho_env_value (B@V) e"
  shows "ho_value_ge A (ho_weak_source_interpretation S V B I e t) (ho_weak_source_interpretation S V B I e u)"
proof -
  have zl: "ho_zero_arity_pattern l" and zr: "ho_zero_arity_pattern r"
    using zero member unfolding ho_zero_arity_rules_def by auto
  obtain T where l: "ho_typeof S G [] (ho_erase_pattern l)=Some T"
    and r: "ho_typeof S G [] (ho_erase_pattern r)=Some T"
    and order: "\<And>d. ho_env_value G d \<Longrightarrow>
      ho_value_ge T (ho_weak_source_interpretation S G [] I d (ho_erase_pattern l))
        (ho_weak_source_interpretation S G [] I d (ho_erase_pattern r))"
    using orient unfolding ho_weak_rule_def by blast
  have ts: "t=ho_subst s 0 (ho_erase_pattern l)" and us: "u=ho_subst s 0 (ho_erase_pattern r)"
    using lhs rhs ho_zero_arity_instantiate[OF zl] ho_zero_arity_instantiate[OF zr] by auto
  have lt: "ho_typeof S V B t=Some T"
    using ho_typeof_free_subst_context[OF l subst] by (simp add: ts)
  have eq: "A=T" using ty lt by simp
  show ?thesis unfolding ts us eq by (rule ho_weak_source_free_instance_ge[OF l r subst closed cv ev order])
qed

lemma ho_weak_source_app:
  "ho_typeof S V B f=Some (HArrow A C) \<Longrightarrow>
    ho_weak_source_interpretation S V B I e (HApp f x) =
    ho_plain_app A C (ho_weak_source_interpretation S V B I e f) (ho_weak_source_interpretation S V B I e x)"
  by (simp add: ho_weak_source_interpretation_def)

lemma ho_weak_source_abs_path:
  assumes ty: "ho_typeof S V (A#B) t=Some C" and closed: "ho_interpretation_closed I"
  shows "beta\<^sup>*\<^sup>* (App (ho_weak_source_interpretation S V B I e (HAbs A t)) x)
    (ho_weak_source_interpretation S V (A#B) I (ho_env_cons x e) t)"
  unfolding ho_weak_source_interpretation_def
  using ho_weak_evaluate_abstraction_beta[OF closed, of e A C "ho_compile S V (A#B) t" x]
  by (simp add: ty r_into_rtranclp)

theorem ho_weak_source_step_ge:
  assumes step: "ho_step S V R B t u" and zero: "ho_zero_arity_rules R"
    and closed: "ho_interpretation_closed I" and cv: "ho_env_value S I"
    and rules: "\<And>G l r. (G,l,r)\<in>set R \<Longrightarrow> ho_weak_rule S I G l r"
    and ty: "ho_typeof S V B t=Some A" and ev: "ho_env_value (B@V) e"
  shows "ho_value_ge A (ho_weak_source_interpretation S V B I e t) (ho_weak_source_interpretation S V B I e u)"
using step ty ev
proof (induction arbitrary: A e rule: ho_step.induct)
  case (rule G l r B s t u)
  show ?case by (rule ho_weak_source_rule_ge[OF rule.hyps(1) zero rule.hyps(3-5)
    rule.prems(1) rules[OF rule.hyps(1)] closed cv rule.prems(2)])
next
  case (beta B T t u)
  obtain C where body: "ho_typeof S V (T#B) t=Some C" and arg: "ho_typeof S V B u=Some T"
    and a: "A=C" using beta.prems(1) by (auto split: option.splits ho_type.splits if_splits)
  show ?case unfolding a by (rule ho_weak_source_beta_ge[OF body arg closed cv beta.prems(2)])
next
  case (app_left B t u x)
  obtain T where f: "ho_typeof S V B t=Some (HArrow T A)" and x: "ho_typeof S V B x=Some T"
    using app_left.prems(1) by (auto split: option.splits ho_type.splits if_splits)
  have u: "ho_typeof S V B u=Some (HArrow T A)"
    by (rule ho_zero_arity_step_type[OF app_left.hyps zero f])
  have tv: "ho_value (HArrow T A) (ho_weak_source_interpretation S V B I e t)"
    by (rule ho_weak_source_interpretation_value[OF f closed cv app_left.prems(2)])
  have uv: "ho_value (HArrow T A) (ho_weak_source_interpretation S V B I e u)"
    by (rule ho_weak_source_interpretation_value[OF u closed cv app_left.prems(2)])
  have xv: "ho_value T (ho_weak_source_interpretation S V B I e x)"
    by (rule ho_weak_source_interpretation_value[OF x closed cv app_left.prems(2)])
  have ih: "ho_value_ge (HArrow T A) (ho_weak_source_interpretation S V B I e t)
      (ho_weak_source_interpretation S V B I e u)" by (rule app_left.IH[OF f app_left.prems(2)])
  show ?case unfolding ho_weak_source_app[OF f] ho_weak_source_app[OF u]
    by (rule ho_plain_app_ge[OF tv uv xv xv ih ho_value_ge_refl[OF xv]])
next
  case (app_right B t u x)
  obtain T where f: "ho_typeof S V B x=Some (HArrow T A)" and t: "ho_typeof S V B t=Some T"
    using app_right.prems(1) by (auto split: option.splits ho_type.splits if_splits)
  have u: "ho_typeof S V B u=Some T" by (rule ho_zero_arity_step_type[OF app_right.hyps zero t])
  have fv: "ho_value (HArrow T A) (ho_weak_source_interpretation S V B I e x)"
    by (rule ho_weak_source_interpretation_value[OF f closed cv app_right.prems(2)])
  have tv: "ho_value T (ho_weak_source_interpretation S V B I e t)"
    by (rule ho_weak_source_interpretation_value[OF t closed cv app_right.prems(2)])
  have uv: "ho_value T (ho_weak_source_interpretation S V B I e u)"
    by (rule ho_weak_source_interpretation_value[OF u closed cv app_right.prems(2)])
  have ih: "ho_value_ge T (ho_weak_source_interpretation S V B I e t)
      (ho_weak_source_interpretation S V B I e u)" by (rule app_right.IH[OF t app_right.prems(2)])
  show ?case unfolding ho_weak_source_app[OF f]
    by (rule ho_plain_app_ge[OF fv fv tv uv ho_value_ge_refl[OF fv] ih])
next
  case (abs T B t u)
  obtain C where body: "ho_typeof S V (T#B) t=Some C" and a: "A=HArrow T C"
    using abs.prems(1) by (auto split: option.splits)
  have u: "ho_typeof S V (T#B) u=Some C" by (rule ho_zero_arity_step_type[OF abs.hyps zero body])
  show ?case unfolding a ho_value_ge.simps(2)
  proof (intro allI impI)
    fix x assume x: "ho_value T x"
    have env: "ho_env_value ((T#B)@V) (ho_env_cons x e)"
      using ho_env_cons_value[OF x abs.prems(2)] by simp
    have ih: "ho_value_ge C (ho_weak_source_interpretation S V (T#B) I (ho_env_cons x e) t)
        (ho_weak_source_interpretation S V (T#B) I (ho_env_cons x e) u)"
      by (rule abs.IH[OF body env])
    have eq: "ho_value_ge C (App (ho_weak_source_interpretation S V B I e (HAbs T t)) x)
        (App (ho_weak_source_interpretation S V B I e (HAbs T u)) x) =
      ho_value_ge C (ho_weak_source_interpretation S V (T#B) I (ho_env_cons x e) t)
        (ho_weak_source_interpretation S V (T#B) I (ho_env_cons x e) u)"
      by (rule ho_ge_beta[OF ho_weak_source_abs_path[OF body closed] ho_weak_source_abs_path[OF u closed]])
    show "ho_value_ge C (App (ho_weak_source_interpretation S V B I e (HAbs T t)) x)
        (App (ho_weak_source_interpretation S V B I e (HAbs T u)) x)" using ih eq by simp
  qed
qed


end
