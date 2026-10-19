theory Higher_Order_Source_Order
  imports Higher_Order_Expression_Bridge Higher_Order_Rule_Removal
begin

fun ho_zero_arity_pattern where
  "ho_zero_arity_pattern (PBound n) = True"
| "ho_zero_arity_pattern (PConst n) = True"
| "ho_zero_arity_pattern (PApp f x) = (ho_zero_arity_pattern f \<and> ho_zero_arity_pattern x)"
| "ho_zero_arity_pattern (PAbs A t) = ho_zero_arity_pattern t"
| "ho_zero_arity_pattern (PMeta n ts) = (ts=[])"

lemma ho_zero_arity_instantiate:
  "ho_zero_arity_pattern p \<Longrightarrow> ho_instantiate s d p=Some (ho_subst s d (ho_erase_pattern p))"
  by (induction p arbitrary: d) auto

definition ho_zero_arity_rules where
  "ho_zero_arity_rules R \<longleftrightarrow> (\<forall>(G,l,r)\<in>set R. ho_zero_arity_pattern l \<and> ho_zero_arity_pattern r)"

lemma ho_zero_arity_rule_type:
  assumes member: "(G,l,r)\<in>set R" and zero: "ho_zero_arity_rules R"
    and rule_type: "ho_rule_welltyped S (G,l,r)" and subst: "ho_typed_subst S V B G s"
    and lhs: "ho_instantiate s 0 l=Some t" and rhs: "ho_instantiate s 0 r=Some u"
  shows "\<exists>A. ho_typeof S V B t=Some A \<and> ho_typeof S V B u=Some A"
proof -
  have zl: "ho_zero_arity_pattern l" and zr: "ho_zero_arity_pattern r"
    using zero member unfolding ho_zero_arity_rules_def by auto
  obtain A where l: "ho_typeof S G [] (ho_erase_pattern l)=Some A"
    and r: "ho_typeof S G [] (ho_erase_pattern r)=Some A"
    using rule_type by (auto simp: ho_rule_welltyped_def split: option.splits)
  have ts: "t=ho_subst s 0 (ho_erase_pattern l)" and us: "u=ho_subst s 0 (ho_erase_pattern r)"
    using lhs rhs ho_zero_arity_instantiate[OF zl] ho_zero_arity_instantiate[OF zr] by auto
  have lt: "ho_typeof S V B t=Some A"
    using ho_typeof_free_subst_context[OF l subst] by (simp add: ts)
  have rt: "ho_typeof S V B u=Some A"
    using ho_typeof_free_subst_context[OF r subst] by (simp add: us)
  show ?thesis using lt rt by blast
qed

theorem ho_zero_arity_step_type:
  assumes step: "ho_step S V R B t u" and zero: "ho_zero_arity_rules R"
    and ty: "ho_typeof S V B t=Some A"
  shows "ho_typeof S V B u=Some A"
using step ty
proof (induction arbitrary: A rule: ho_step.induct)
  case (rule G l r B s t u)
  from ho_zero_arity_rule_type[OF rule.hyps(1) zero rule.hyps(2-5)] rule.prems
  show ?case by auto
next
  case (beta B T t u)
  obtain C where body: "ho_typeof S V (T#B) t=Some C" and arg: "ho_typeof S V B u=Some T"
    and a: "A=C" using beta.prems by (auto split: option.splits ho_type.splits if_splits)
  show ?case using ho_typeof_beta_context[where B="[]", simplified, OF body arg] a by simp
next
  case (app_left B t u x)
  then show ?case by (auto split: option.splits ho_type.splits if_splits)
next
  case (app_right B t u x)
  then show ?case by (auto split: option.splits ho_type.splits if_splits)
next
  case (abs T B t u)
  then show ?case by (auto split: option.splits)
qed

lemma ho_source_free_instance_ge:
  assumes l: "ho_typeof S G [] l=Some A" and r: "ho_typeof S G [] r=Some A"
    and subst: "ho_typed_subst S V B G s"
    and closed: "ho_interpretation_closed I" and cv: "ho_env_value S I"
    and ev: "ho_env_value (B@V) e"
    and orient: "\<And>d. ho_env_value G d \<Longrightarrow>
      ho_value_ge A (ho_source_interpretation S G [] I d l) (ho_source_interpretation S G [] I d r)"
  shows "ho_value_ge A (ho_source_interpretation S V B I e (ho_subst s 0 l))
    (ho_source_interpretation S V B I e (ho_subst s 0 r))"
proof -
  have sty: "ho_expression_type S (B@V) (ho_compile S V B (s n)) (G!n)"
    if "n<length G" for n
    by (rule ho_compile_type) (use subst that in \<open>simp add: ho_typed_subst_def\<close>)
  show ?thesis unfolding ho_source_interpretation_def
    ho_compile_free_subst[OF l subst] ho_compile_free_subst[OF r subst]
    by (rule ho_evaluate_instance_ge[OF closed cv ev sty])
       (auto intro: orient[unfolded ho_source_interpretation_def])
qed

lemma ho_source_free_instance_gt:
  assumes l: "ho_typeof S G [] l=Some A" and r: "ho_typeof S G [] r=Some A"
    and subst: "ho_typed_subst S V B G s"
    and closed: "ho_interpretation_closed I" and cv: "ho_env_value S I"
    and ev: "ho_env_value (B@V) e"
    and orient: "\<And>d. ho_env_value G d \<Longrightarrow>
      ho_value_gt A (ho_source_interpretation S G [] I d l) (ho_source_interpretation S G [] I d r)"
  shows "ho_value_gt A (ho_source_interpretation S V B I e (ho_subst s 0 l))
    (ho_source_interpretation S V B I e (ho_subst s 0 r))"
proof -
  have sty: "ho_expression_type S (B@V) (ho_compile S V B (s n)) (G!n)"
    if "n<length G" for n
    by (rule ho_compile_type) (use subst that in \<open>simp add: ho_typed_subst_def\<close>)
  show ?thesis unfolding ho_source_interpretation_def
    ho_compile_free_subst[OF l subst] ho_compile_free_subst[OF r subst]
    by (rule ho_evaluate_instance_gt[OF closed cv ev sty])
       (auto intro: orient[unfolded ho_source_interpretation_def])
qed

lemma ho_source_beta_ge:
  assumes body: "ho_typeof S V (A#B) t=Some C" and arg: "ho_typeof S V B x=Some A"
    and closed: "ho_interpretation_closed I" and cv: "ho_env_value S I"
    and ev: "ho_env_value (B@V) e"
  shows "ho_value_ge C (ho_source_interpretation S V B I e (HApp (HAbs A t) x))
    (ho_source_interpretation S V B I e (ho_beta_subst x 0 t))"
proof -
  have bt: "ho_expression_type S (A#(B@V)) (ho_compile S V (A#B) t) C"
    using ho_compile_type[OF body] by simp
  have order: "ho_value_ge C
      (ho_evaluate I e (HEApp A C (HEAbs A C (ho_compile S V (A#B) t)) (ho_compile S V B x)))
      (ho_evaluate I e (ho_expr_beta_subst (ho_compile S V B x) (ho_compile S V (A#B) t)))"
    by (rule ho_evaluate_beta_weak[OF bt ho_compile_type[OF arg] closed cv ev])
  show ?thesis using order
    by (simp add: ho_source_interpretation_def body ho_compile_beta[OF body arg])
qed

definition ho_rule_weak where
  "ho_rule_weak S I G l r \<longleftrightarrow>
    (\<exists>A. ho_typeof S G [] (ho_erase_pattern l)=Some A \<and>
      ho_typeof S G [] (ho_erase_pattern r)=Some A \<and>
      (\<forall>e. ho_env_value G e \<longrightarrow>
        ho_value_ge A (ho_source_interpretation S G [] I e (ho_erase_pattern l))
          (ho_source_interpretation S G [] I e (ho_erase_pattern r))))"

lemma ho_source_rule_ge:
  assumes member: "(G,l,r)\<in>set R" and zero: "ho_zero_arity_rules R"
    and subst: "ho_typed_subst S V B G s"
    and lhs: "ho_instantiate s 0 l=Some t" and rhs: "ho_instantiate s 0 r=Some u"
    and ty: "ho_typeof S V B t=Some A" and orient: "ho_rule_weak S I G l r"
    and closed: "ho_interpretation_closed I" and cv: "ho_env_value S I"
    and ev: "ho_env_value (B@V) e"
  shows "ho_value_ge A (ho_source_interpretation S V B I e t) (ho_source_interpretation S V B I e u)"
proof -
  have zl: "ho_zero_arity_pattern l" and zr: "ho_zero_arity_pattern r"
    using zero member unfolding ho_zero_arity_rules_def by auto
  obtain T where l: "ho_typeof S G [] (ho_erase_pattern l)=Some T"
    and r: "ho_typeof S G [] (ho_erase_pattern r)=Some T"
    and order: "\<And>d. ho_env_value G d \<Longrightarrow>
      ho_value_ge T (ho_source_interpretation S G [] I d (ho_erase_pattern l))
        (ho_source_interpretation S G [] I d (ho_erase_pattern r))"
    using orient unfolding ho_rule_weak_def by blast
  have ts: "t=ho_subst s 0 (ho_erase_pattern l)" and us: "u=ho_subst s 0 (ho_erase_pattern r)"
    using lhs rhs ho_zero_arity_instantiate[OF zl] ho_zero_arity_instantiate[OF zr] by auto
  have lt: "ho_typeof S V B t=Some T"
    using ho_typeof_free_subst_context[OF l subst] by (simp add: ts)
  have eq: "A=T" using ty lt by simp
  show ?thesis unfolding ts us eq by (rule ho_source_free_instance_ge[OF l r subst closed cv ev order])
qed

lemma ho_source_app:
  "ho_typeof S V B f=Some (HArrow A C) \<Longrightarrow>
    ho_source_interpretation S V B I e (HApp f x) =
    ho_sem_app A C (ho_source_interpretation S V B I e f) (ho_source_interpretation S V B I e x)"
  by (simp add: ho_source_interpretation_def)

lemma ho_source_abs_path:
  assumes ty: "ho_typeof S V (A#B) t=Some C" and closed: "ho_interpretation_closed I"
  shows "beta\<^sup>*\<^sup>* (App (ho_source_interpretation S V B I e (HAbs A t)) x)
    (ho_source_interpretation S V (A#B) I (ho_env_cons x e) t)"
  unfolding ho_source_interpretation_def
  using ho_evaluate_abstraction_beta[OF closed, of e A C "ho_compile S V (A#B) t" x]
  by (simp add: ty r_into_rtranclp)

theorem ho_source_step_ge:
  assumes step: "ho_step S V R B t u" and zero: "ho_zero_arity_rules R"
    and closed: "ho_interpretation_closed I" and cv: "ho_env_value S I"
    and rules: "\<And>G l r. (G,l,r)\<in>set R \<Longrightarrow> ho_rule_weak S I G l r"
    and ty: "ho_typeof S V B t=Some A" and ev: "ho_env_value (B@V) e"
  shows "ho_value_ge A (ho_source_interpretation S V B I e t) (ho_source_interpretation S V B I e u)"
using step ty ev
proof (induction arbitrary: A e rule: ho_step.induct)
  case (rule G l r B s t u)
  show ?case by (rule ho_source_rule_ge[OF rule.hyps(1) zero rule.hyps(3-5)
    rule.prems(1) rules[OF rule.hyps(1)] closed cv rule.prems(2)])
next
  case (beta B T t u)
  obtain C where body: "ho_typeof S V (T#B) t=Some C" and arg: "ho_typeof S V B u=Some T"
    and a: "A=C" using beta.prems(1) by (auto split: option.splits ho_type.splits if_splits)
  show ?case unfolding a by (rule ho_source_beta_ge[OF body arg closed cv beta.prems(2)])
next
  case (app_left B t u x)
  obtain T where f: "ho_typeof S V B t=Some (HArrow T A)" and x: "ho_typeof S V B x=Some T"
    using app_left.prems(1) by (auto split: option.splits ho_type.splits if_splits)
  have u: "ho_typeof S V B u=Some (HArrow T A)"
    by (rule ho_zero_arity_step_type[OF app_left.hyps zero f])
  have tv: "ho_value (HArrow T A) (ho_source_interpretation S V B I e t)"
    by (rule ho_source_interpretation_value[OF f closed cv app_left.prems(2)])
  have uv: "ho_value (HArrow T A) (ho_source_interpretation S V B I e u)"
    by (rule ho_source_interpretation_value[OF u closed cv app_left.prems(2)])
  have xv: "ho_value T (ho_source_interpretation S V B I e x)"
    by (rule ho_source_interpretation_value[OF x closed cv app_left.prems(2)])
  have ih: "ho_value_ge (HArrow T A) (ho_source_interpretation S V B I e t)
      (ho_source_interpretation S V B I e u)" by (rule app_left.IH[OF f app_left.prems(2)])
  show ?case unfolding ho_source_app[OF f] ho_source_app[OF u]
    by (rule ho_sem_app_ge[OF tv uv xv xv ih ho_value_ge_refl[OF xv]])
next
  case (app_right B t u x)
  obtain T where f: "ho_typeof S V B x=Some (HArrow T A)" and t: "ho_typeof S V B t=Some T"
    using app_right.prems(1) by (auto split: option.splits ho_type.splits if_splits)
  have u: "ho_typeof S V B u=Some T" by (rule ho_zero_arity_step_type[OF app_right.hyps zero t])
  have fv: "ho_value (HArrow T A) (ho_source_interpretation S V B I e x)"
    by (rule ho_source_interpretation_value[OF f closed cv app_right.prems(2)])
  have tv: "ho_value T (ho_source_interpretation S V B I e t)"
    by (rule ho_source_interpretation_value[OF t closed cv app_right.prems(2)])
  have uv: "ho_value T (ho_source_interpretation S V B I e u)"
    by (rule ho_source_interpretation_value[OF u closed cv app_right.prems(2)])
  have ih: "ho_value_ge T (ho_source_interpretation S V B I e t)
      (ho_source_interpretation S V B I e u)" by (rule app_right.IH[OF t app_right.prems(2)])
  show ?case unfolding ho_source_app[OF f]
    by (rule ho_sem_app_ge[OF fv fv tv uv ho_value_ge_refl[OF fv] ih])
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
    have ih: "ho_value_ge C (ho_source_interpretation S V (T#B) I (ho_env_cons x e) t)
        (ho_source_interpretation S V (T#B) I (ho_env_cons x e) u)"
      by (rule abs.IH[OF body env])
    have eq: "ho_value_ge C (App (ho_source_interpretation S V B I e (HAbs T t)) x)
        (App (ho_source_interpretation S V B I e (HAbs T u)) x) =
      ho_value_ge C (ho_source_interpretation S V (T#B) I (ho_env_cons x e) t)
        (ho_source_interpretation S V (T#B) I (ho_env_cons x e) u)"
      by (rule ho_ge_beta[OF ho_source_abs_path[OF body closed] ho_source_abs_path[OF u closed]])
    show "ho_value_ge C (App (ho_source_interpretation S V B I e (HAbs T t)) x)
        (App (ho_source_interpretation S V B I e (HAbs T u)) x)" using ih eq by simp
  qed
qed

definition ho_rule_strict where
  "ho_rule_strict S I G l r \<longleftrightarrow>
    (\<exists>A. ho_typeof S G [] (ho_erase_pattern l)=Some A \<and>
      ho_typeof S G [] (ho_erase_pattern r)=Some A \<and>
      (\<forall>e. ho_env_value G e \<longrightarrow>
        ho_value_gt A (ho_source_interpretation S G [] I e (ho_erase_pattern l))
          (ho_source_interpretation S G [] I e (ho_erase_pattern r))))"

lemma ho_source_rule_gt:
  assumes member: "(G,l,r)\<in>set R" and zero: "ho_zero_arity_rules R"
    and subst: "ho_typed_subst S V B G s"
    and lhs: "ho_instantiate s 0 l=Some t" and rhs: "ho_instantiate s 0 r=Some u"
    and ty: "ho_typeof S V B t=Some A" and orient: "ho_rule_strict S I G l r"
    and closed: "ho_interpretation_closed I" and cv: "ho_env_value S I"
    and ev: "ho_env_value (B@V) e"
  shows "ho_value_gt A (ho_source_interpretation S V B I e t) (ho_source_interpretation S V B I e u)"
proof -
  have zl: "ho_zero_arity_pattern l" and zr: "ho_zero_arity_pattern r"
    using zero member unfolding ho_zero_arity_rules_def by auto
  obtain T where l: "ho_typeof S G [] (ho_erase_pattern l)=Some T"
    and r: "ho_typeof S G [] (ho_erase_pattern r)=Some T"
    and order: "\<And>d. ho_env_value G d \<Longrightarrow>
      ho_value_gt T (ho_source_interpretation S G [] I d (ho_erase_pattern l))
        (ho_source_interpretation S G [] I d (ho_erase_pattern r))"
    using orient unfolding ho_rule_strict_def by blast
  have ts: "t=ho_subst s 0 (ho_erase_pattern l)" and us: "u=ho_subst s 0 (ho_erase_pattern r)"
    using lhs rhs ho_zero_arity_instantiate[OF zl] ho_zero_arity_instantiate[OF zr] by auto
  have lt: "ho_typeof S V B t=Some T"
    using ho_typeof_free_subst_context[OF l subst] by (simp add: ts)
  have eq: "A=T" using ty lt by simp
  show ?thesis unfolding ts us eq by (rule ho_source_free_instance_gt[OF l r subst closed cv ev order])
qed

theorem ho_source_step_gt:
  assumes step: "ho_step S V R B t u" and zero: "ho_zero_arity_rules R"
    and closed: "ho_interpretation_closed I" and cv: "ho_env_value S I"
    and rules: "\<And>G l r. (G,l,r)\<in>set R \<Longrightarrow> (G,l,r)\<notin>set R' \<Longrightarrow> ho_rule_strict S I G l r"
    and ty: "ho_typeof S V B t=Some A" and ev: "ho_env_value (B@V) e"
    and absent: "\<not>ho_step S V R' B t u"
  shows "ho_value_gt A (ho_source_interpretation S V B I e t) (ho_source_interpretation S V B I e u)"
using step ty ev absent
proof (induction arbitrary: A e rule: ho_step.induct)
  case (rule G l r B s t u)
  have missing: "(G,l,r)\<notin>set R'" using rule.prems(3) rule.hyps(2-5)
    by (blast intro: ho_step.rule)
  show ?case by (rule ho_source_rule_gt[OF rule.hyps(1) zero rule.hyps(3-5)
    rule.prems(1) rules[OF rule.hyps(1) missing] closed cv rule.prems(2)])
next
  case (beta B T t u)
  then show ?case using ho_step.beta by blast
next
  case (app_left B t u x)
  obtain T where f: "ho_typeof S V B t=Some (HArrow T A)" and x: "ho_typeof S V B x=Some T"
    using app_left.prems(1) by (auto split: option.splits ho_type.splits if_splits)
  have u: "ho_typeof S V B u=Some (HArrow T A)"
    by (rule ho_zero_arity_step_type[OF app_left.hyps zero f])
  have xv: "ho_value T (ho_source_interpretation S V B I e x)"
    by (rule ho_source_interpretation_value[OF x closed cv app_left.prems(2)])
  have no: "\<not>ho_step S V R' B t u" using app_left.prems(3) by (blast intro: ho_step.app_left)
  have ih: "ho_value_gt (HArrow T A) (ho_source_interpretation S V B I e t)
      (ho_source_interpretation S V B I e u)" by (rule app_left.IH[OF f app_left.prems(2) no])
  show ?case unfolding ho_source_app[OF f] ho_source_app[OF u]
    by (rule ho_sem_app_gt_left[OF xv ih])
next
  case (app_right B t u x)
  obtain T where f: "ho_typeof S V B x=Some (HArrow T A)" and t: "ho_typeof S V B t=Some T"
    using app_right.prems(1) by (auto split: option.splits ho_type.splits if_splits)
  have u: "ho_typeof S V B u=Some T" by (rule ho_zero_arity_step_type[OF app_right.hyps zero t])
  have fv: "ho_value (HArrow T A) (ho_source_interpretation S V B I e x)"
    by (rule ho_source_interpretation_value[OF f closed cv app_right.prems(2)])
  have tv: "ho_value T (ho_source_interpretation S V B I e t)"
    by (rule ho_source_interpretation_value[OF t closed cv app_right.prems(2)])
  have uv: "ho_value T (ho_source_interpretation S V B I e u)"
    by (rule ho_source_interpretation_value[OF u closed cv app_right.prems(2)])
  have no: "\<not>ho_step S V R' B t u" using app_right.prems(3) by (blast intro: ho_step.app_right)
  have ih: "ho_value_gt T (ho_source_interpretation S V B I e t)
      (ho_source_interpretation S V B I e u)" by (rule app_right.IH[OF t app_right.prems(2) no])
  show ?case unfolding ho_source_app[OF f]
    by (rule ho_sem_app_gt_right[OF fv tv uv ih])
next
  case (abs T B t u)
  obtain C where body: "ho_typeof S V (T#B) t=Some C" and a: "A=HArrow T C"
    using abs.prems(1) by (auto split: option.splits)
  have u: "ho_typeof S V (T#B) u=Some C" by (rule ho_zero_arity_step_type[OF abs.hyps zero body])
  have no: "\<not>ho_step S V R' (T#B) t u" using abs.prems(3) by (blast intro: ho_step.abs)
  show ?case unfolding a ho_value_gt.simps(2)
  proof (intro allI impI)
    fix x assume x: "ho_value T x"
    have env: "ho_env_value ((T#B)@V) (ho_env_cons x e)"
      using ho_env_cons_value[OF x abs.prems(2)] by simp
    have ih: "ho_value_gt C (ho_source_interpretation S V (T#B) I (ho_env_cons x e) t)
        (ho_source_interpretation S V (T#B) I (ho_env_cons x e) u)"
      by (rule abs.IH[OF body env no])
    have eq: "ho_value_gt C (App (ho_source_interpretation S V B I e (HAbs T t)) x)
        (App (ho_source_interpretation S V B I e (HAbs T u)) x) =
      ho_value_gt C (ho_source_interpretation S V (T#B) I (ho_env_cons x e) t)
        (ho_source_interpretation S V (T#B) I (ho_env_cons x e) u)"
      by (rule ho_gt_beta[OF ho_source_abs_path[OF body closed] ho_source_abs_path[OF u closed]])
    show "ho_value_gt C (App (ho_source_interpretation S V B I e (HAbs T t)) x)
        (App (ho_source_interpretation S V B I e (HAbs T u)) x)" using ih eq by simp
  qed
qed

theorem ho_semantic_rule_removal:
  assumes residual: "wf ((ho_relation S V R' A)\<inverse>)"
    and zero: "ho_zero_arity_rules R" and closed: "ho_interpretation_closed I"
    and cv: "ho_env_value S I" and ev: "ho_env_value V e"
    and weak: "\<And>G l r. (G,l,r)\<in>set R \<Longrightarrow> ho_rule_weak S I G l r"
    and strict: "\<And>G l r. (G,l,r)\<in>set R \<Longrightarrow> (G,l,r)\<notin>set R' \<Longrightarrow> ho_rule_strict S I G l r"
  shows "wf ((ho_relation S V R A)\<inverse>)"
proof (rule ho_typed_rule_removal[where T=A and I="ho_source_interpretation S V [] I e", OF residual])
  fix t u assume pair: "(t,u)\<in>ho_relation S V R A"
  then have step: "ho_step S V R [] t u" and ty: "ho_typeof S V [] t=Some A"
    by (auto simp: ho_relation_def)
  have env: "ho_env_value ([]@V) e" using ev by simp
  show "ho_observe A (ho_source_interpretation S V [] I e u) \<le>
      ho_observe A (ho_source_interpretation S V [] I e t)"
    by (rule ho_value_ge_observe[OF ho_source_step_ge[OF step zero closed cv weak ty env]])
next
  fix t u assume pair: "(t,u)\<in>ho_relation S V R A" and missing: "(t,u)\<notin>ho_relation S V R' A"
  then have step: "ho_step S V R [] t u" and ty: "ho_typeof S V [] t=Some A"
    and no: "\<not>ho_step S V R' [] t u" by (auto simp: ho_relation_def)
  have env: "ho_env_value ([]@V) e" using ev by simp
  show "ho_value_gt A (ho_source_interpretation S V [] I e t) (ho_source_interpretation S V [] I e u)"
    by (rule ho_source_step_gt[OF step zero closed cv strict ty env no])
qed

end
