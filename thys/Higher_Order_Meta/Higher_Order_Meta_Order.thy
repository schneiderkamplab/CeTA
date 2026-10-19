theory Higher_Order_Meta_Order
  imports Higher_Order_Meta_Interpretation
begin

definition ho_meta_rule_weak where
  "ho_meta_rule_weak S I G l r \<longleftrightarrow>
    (\<exists>A. ho_typeof S G [] (ho_erase_pattern l)=Some A \<and>
      ho_typeof S G [] (ho_erase_pattern r)=Some A \<and>
      (\<forall>e. ho_env_value G e \<longrightarrow>
        ho_value_ge A (ho_pattern_interpretation S G [] I e e l)
          (ho_pattern_interpretation S G [] I e e r)))"

lemma ho_source_meta_rule_ge:
  assumes subst: "ho_typed_subst S V B G s"
    and lhs: "ho_instantiate s 0 l=Some t" and rhs: "ho_instantiate s 0 r=Some u"
    and ty: "ho_typeof S V B t=Some A" and orient: "ho_meta_rule_weak S I G l r"
    and closed: "ho_interpretation_closed I" and cv: "ho_env_value S I"
    and ev: "ho_env_value (B@V) e"
  shows "ho_value_ge A (ho_source_interpretation S V B I e t) (ho_source_interpretation S V B I e u)"
proof -
  obtain T where l: "ho_typeof S G [] (ho_erase_pattern l)=Some T"
    and r: "ho_typeof S G [] (ho_erase_pattern r)=Some T"
    and order: "\<And>d. ho_env_value G d \<Longrightarrow>
      ho_value_ge T (ho_pattern_interpretation S G [] I d d l)
        (ho_pattern_interpretation S G [] I d d r)"
    using orient unfolding ho_meta_rule_weak_def by blast
  let ?d = "\<lambda>n. ho_source_interpretation S V B I e (s n)"
  have vals: "ho_env_value G ?d"
    unfolding ho_env_value_def
    by (intro allI impI ho_source_interpretation_value[OF _ closed cv ev])
       (use subst in \<open>auto simp: ho_typed_subst_def\<close>)
  have lt: "ho_typeof S V B t=Some T"
    using ho_instantiate_type[OF l subst] lhs by simp
  have eq: "A=T" using ty lt by simp
  have left: "beta\<^sup>*\<^sup>* (ho_pattern_interpretation S G [] I ?d ?d l)
      (ho_source_interpretation S V B I e t)"
    using ho_pattern_interpretation_instance[OF l subst _ closed, of t ?d e ?d] lhs by simp
  have right: "beta\<^sup>*\<^sup>* (ho_pattern_interpretation S G [] I ?d ?d r)
      (ho_source_interpretation S V B I e u)"
    using ho_pattern_interpretation_instance[OF r subst _ closed, of u ?d e ?d] rhs by simp
  show ?thesis using ho_ge_beta[OF left right, of T] order[OF vals] by (simp add: eq)
qed

definition ho_meta_rule_strict where
  "ho_meta_rule_strict S I G l r \<longleftrightarrow>
    (\<exists>A. ho_typeof S G [] (ho_erase_pattern l)=Some A \<and>
      ho_typeof S G [] (ho_erase_pattern r)=Some A \<and>
      (\<forall>e. ho_env_value G e \<longrightarrow>
        ho_value_gt A (ho_pattern_interpretation S G [] I e e l)
          (ho_pattern_interpretation S G [] I e e r)))"

lemma ho_source_meta_rule_gt:
  assumes subst: "ho_typed_subst S V B G s"
    and lhs: "ho_instantiate s 0 l=Some t" and rhs: "ho_instantiate s 0 r=Some u"
    and ty: "ho_typeof S V B t=Some A" and orient: "ho_meta_rule_strict S I G l r"
    and closed: "ho_interpretation_closed I" and cv: "ho_env_value S I"
    and ev: "ho_env_value (B@V) e"
  shows "ho_value_gt A (ho_source_interpretation S V B I e t) (ho_source_interpretation S V B I e u)"
proof -
  obtain T where l: "ho_typeof S G [] (ho_erase_pattern l)=Some T"
    and r: "ho_typeof S G [] (ho_erase_pattern r)=Some T"
    and order: "\<And>d. ho_env_value G d \<Longrightarrow>
      ho_value_gt T (ho_pattern_interpretation S G [] I d d l)
        (ho_pattern_interpretation S G [] I d d r)"
    using orient unfolding ho_meta_rule_strict_def by blast
  let ?d = "\<lambda>n. ho_source_interpretation S V B I e (s n)"
  have vals: "ho_env_value G ?d"
    unfolding ho_env_value_def
    by (intro allI impI ho_source_interpretation_value[OF _ closed cv ev])
       (use subst in \<open>auto simp: ho_typed_subst_def\<close>)
  have lt: "ho_typeof S V B t=Some T"
    using ho_instantiate_type[OF l subst] lhs by simp
  have eq: "A=T" using ty lt by simp
  have left: "beta\<^sup>*\<^sup>* (ho_pattern_interpretation S G [] I ?d ?d l)
      (ho_source_interpretation S V B I e t)"
    using ho_pattern_interpretation_instance[OF l subst _ closed, of t ?d e ?d] lhs by simp
  have right: "beta\<^sup>*\<^sup>* (ho_pattern_interpretation S G [] I ?d ?d r)
      (ho_source_interpretation S V B I e u)"
    using ho_pattern_interpretation_instance[OF r subst _ closed, of u ?d e ?d] rhs by simp
  show ?thesis using ho_gt_beta[OF left right, of T] order[OF vals] by (simp add: eq)
qed

theorem ho_source_meta_step_ge:
  assumes step: "ho_step S V R B t u"
    and closed: "ho_interpretation_closed I" and cv: "ho_env_value S I"
    and rules: "\<And>G l r. (G,l,r)\<in>set R \<Longrightarrow> ho_meta_rule_weak S I G l r"
    and ty: "ho_typeof S V B t=Some A" and ev: "ho_env_value (B@V) e"
  shows "ho_value_ge A (ho_source_interpretation S V B I e t) (ho_source_interpretation S V B I e u)"
using step ty ev
proof (induction arbitrary: A e rule: ho_step.induct)
  case (rule G l r B s t u)
  show ?case by (rule ho_source_meta_rule_ge[OF rule.hyps(3-5)
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
    by (rule ho_general_step_type[OF app_left.hyps f])
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
  have u: "ho_typeof S V B u=Some T" by (rule ho_general_step_type[OF app_right.hyps t])
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
  have u: "ho_typeof S V (T#B) u=Some C" by (rule ho_general_step_type[OF abs.hyps body])
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

theorem ho_source_meta_step_gt:
  assumes step: "ho_step S V R B t u"
    and closed: "ho_interpretation_closed I" and cv: "ho_env_value S I"
    and rules: "\<And>G l r. (G,l,r)\<in>set R \<Longrightarrow> (G,l,r)\<notin>set R' \<Longrightarrow> ho_meta_rule_strict S I G l r"
    and ty: "ho_typeof S V B t=Some A" and ev: "ho_env_value (B@V) e"
    and absent: "\<not>ho_step S V R' B t u"
  shows "ho_value_gt A (ho_source_interpretation S V B I e t) (ho_source_interpretation S V B I e u)"
using step ty ev absent
proof (induction arbitrary: A e rule: ho_step.induct)
  case (rule G l r B s t u)
  have missing: "(G,l,r)\<notin>set R'" using rule.prems(3) rule.hyps(2-5)
    by (blast intro: ho_step.rule)
  show ?case by (rule ho_source_meta_rule_gt[OF rule.hyps(3-5)
    rule.prems(1) rules[OF rule.hyps(1) missing] closed cv rule.prems(2)])
next
  case (beta B T t u)
  then show ?case using ho_step.beta by blast
next
  case (app_left B t u x)
  obtain T where f: "ho_typeof S V B t=Some (HArrow T A)" and x: "ho_typeof S V B x=Some T"
    using app_left.prems(1) by (auto split: option.splits ho_type.splits if_splits)
  have u: "ho_typeof S V B u=Some (HArrow T A)"
    by (rule ho_general_step_type[OF app_left.hyps f])
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
  have u: "ho_typeof S V B u=Some T" by (rule ho_general_step_type[OF app_right.hyps t])
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
  have u: "ho_typeof S V (T#B) u=Some C" by (rule ho_general_step_type[OF abs.hyps body])
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

theorem ho_meta_semantic_rule_removal:
  assumes residual: "wf ((ho_relation S V R' A)\<inverse>)"
    and closed: "ho_interpretation_closed I"
    and cv: "ho_env_value S I" and ev: "ho_env_value V e"
    and weak: "\<And>G l r. (G,l,r)\<in>set R \<Longrightarrow> ho_meta_rule_weak S I G l r"
    and strict: "\<And>G l r. (G,l,r)\<in>set R \<Longrightarrow> (G,l,r)\<notin>set R' \<Longrightarrow> ho_meta_rule_strict S I G l r"
  shows "wf ((ho_relation S V R A)\<inverse>)"
proof (rule ho_typed_rule_removal[where T=A and I="ho_source_interpretation S V [] I e", OF residual])
  fix t u assume pair: "(t,u)\<in>ho_relation S V R A"
  then have step: "ho_step S V R [] t u" and ty: "ho_typeof S V [] t=Some A"
    by (auto simp: ho_relation_def)
  have env: "ho_env_value ([]@V) e" using ev by simp
  show "ho_observe A (ho_source_interpretation S V [] I e u) \<le>
      ho_observe A (ho_source_interpretation S V [] I e t)"
    by (rule ho_value_ge_observe[OF ho_source_meta_step_ge[OF step closed cv weak ty env]])
next
  fix t u assume pair: "(t,u)\<in>ho_relation S V R A" and missing: "(t,u)\<notin>ho_relation S V R' A"
  then have step: "ho_step S V R [] t u" and ty: "ho_typeof S V [] t=Some A"
    and no: "\<not>ho_step S V R' [] t u" by (auto simp: ho_relation_def)
  have env: "ho_env_value ([]@V) e" using ev by simp
  show "ho_value_gt A (ho_source_interpretation S V [] I e t) (ho_source_interpretation S V [] I e u)"
    by (rule ho_source_meta_step_gt[OF step closed cv strict ty env no])
qed

end

