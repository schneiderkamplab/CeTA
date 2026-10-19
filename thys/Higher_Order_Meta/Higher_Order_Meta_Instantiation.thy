theory Higher_Order_Meta_Instantiation
  imports "Higher_Order_Modular.Higher_Order_Modular_Checker"
begin

text \<open>Arity-aware meta-instantiation contracts exactly the designated
leading abstractions. Its erased free substitution reduces to the actual
instance by beta alone. This is a typing bridge, not a termination-preserving
first-order erasure: the eventual order must account for those contractions.\<close>

lemma ho_empty_steps_app_left:
  "(ho_step S V [] B)\<^sup>*\<^sup>* t u \<Longrightarrow>
    (ho_step S V [] B)\<^sup>*\<^sup>* (HApp t x) (HApp u x)"
  by (induction rule: rtranclp_induct)
     (auto intro: rtranclp.rtrancl_into_rtrancl ho_step.app_left)

lemma ho_empty_steps_app_right:
  "(ho_step S V [] B)\<^sup>*\<^sup>* t u \<Longrightarrow>
    (ho_step S V [] B)\<^sup>*\<^sup>* (HApp x t) (HApp x u)"
  by (induction rule: rtranclp_induct)
     (auto intro: rtranclp.rtrancl_into_rtrancl ho_step.app_right)

lemma ho_empty_steps_abs:
  "(ho_step S V [] (A#B))\<^sup>*\<^sup>* t u \<Longrightarrow>
    (ho_step S V [] B)\<^sup>*\<^sup>* (HAbs A t) (HAbs A u)"
  by (induction rule: rtranclp_induct)
     (auto intro: rtranclp.rtrancl_into_rtrancl ho_step.abs)

lemma ho_empty_steps_fold:
  assumes "(ho_step S V [] B)\<^sup>*\<^sup>* t u"
    "list_all2 (\<lambda>x y. (ho_step S V [] B)\<^sup>*\<^sup>* x y) xs ys"
  shows "(ho_step S V [] B)\<^sup>*\<^sup>* (foldl HApp t xs) (foldl HApp u ys)"
  using assms(2,1)
proof (induction arbitrary: t u rule: list_all2_induct)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  have "(ho_step S V [] B)\<^sup>*\<^sup>* (HApp t x) (HApp u y)"
    using ho_empty_steps_app_left[OF Cons.prems]
      ho_empty_steps_app_right[OF Cons.hyps(1)] by (rule rtranclp_trans)
  from Cons.IH[OF this] show ?case by simp
qed

lemma ho_meta_apply_beta_path:
  "ho_meta_apply t xs=Some u \<Longrightarrow>
    (ho_step S V [] B)\<^sup>*\<^sup>* (foldl HApp t xs) u"
proof (induction xs arbitrary: t u)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain A b where t: "t=HAbs A b"
    and rest: "ho_meta_apply (ho_beta_subst x 0 b) xs=Some u"
    using Cons.prems by (auto split: ho_term.splits)
  have first: "(ho_step S V [] B)\<^sup>*\<^sup>* (HApp t x) (ho_beta_subst x 0 b)"
    unfolding t by (rule r_into_rtranclp) (rule ho_step.beta)
  have same: "list_all2 (\<lambda>x y. (ho_step S V [] B)\<^sup>*\<^sup>* x y) xs xs"
    by (simp add: list_all2_refl)
  show ?case using ho_empty_steps_fold[OF first same] Cons.IH[OF rest]
    by (auto intro: rtranclp_trans)
qed

lemma ho_subst_fold:
  "ho_subst s d (foldl HApp t xs)=foldl HApp (ho_subst s d t) (map (ho_subst s d) xs)"
  by (induction xs arbitrary: t) simp_all

lemma ho_instantiate_beta_path:
  "ho_instantiate s d p=Some u \<Longrightarrow>
    (ho_step S V [] B)\<^sup>*\<^sup>* (ho_subst s d (ho_erase_pattern p)) u"
proof (induction p arbitrary: d B u)
  case (PApp p q)
  obtain t v where p: "ho_instantiate s d p=Some t"
    and q: "ho_instantiate s d q=Some v" and u: "u=HApp t v"
    using PApp.prems by (auto split: option.splits)
  show ?case unfolding u ho_erase_pattern.simps ho_subst.simps
    using ho_empty_steps_app_left[OF PApp.IH(1)[OF p]]
      ho_empty_steps_app_right[OF PApp.IH(2)[OF q]] by (rule rtranclp_trans)
next
  case (PAbs A p)
  then show ?case by (auto intro: ho_empty_steps_abs)
next
  case (PMeta n ps)
  obtain us where args: "those (map (ho_instantiate s d) ps)=Some us"
    and applied: "ho_meta_apply (ho_lift d 0 (s n)) us=Some u"
    using PMeta.prems by (auto split: option.splits)
  have paths: "list_all2 (\<lambda>x y. (ho_step S V [] B)\<^sup>*\<^sup>* x y)
      (map (\<lambda>p. ho_subst s d (ho_erase_pattern p)) ps) us"
    using args PMeta.IH
  proof (induction ps arbitrary: us)
    case Nil
    then show ?case by simp
  next
    case (Cons p ps)
    then show ?case by (auto split: option.splits)
  qed
  have first: "(ho_step S V [] B)\<^sup>*\<^sup>*
      (ho_subst s d (ho_erase_pattern (PMeta n ps)))
      (foldl HApp (ho_lift d 0 (s n)) us)"
    using ho_empty_steps_fold[OF rtranclp.rtrancl_refl paths, of "ho_lift d 0 (s n)"]
    by (simp add: ho_subst_fold map_map o_def)
  show ?case by (rule rtranclp_trans[OF first ho_meta_apply_beta_path[OF applied]])
qed auto

lemma ho_empty_steps_type:
  "(ho_step S V [] B)\<^sup>*\<^sup>* t u \<Longrightarrow> ho_typeof S V B t=Some A \<Longrightarrow>
    ho_typeof S V B u=Some A"
  by (induction rule: rtranclp_induct)
     (auto intro: ho_zero_arity_step_type simp: ho_zero_arity_rules_def)

theorem ho_instantiate_type:
  assumes pattern: "ho_typeof S G D (ho_erase_pattern p)=Some A"
    and subst: "ho_typed_subst S V B G s"
    and instantiated: "ho_instantiate s (length D) p=Some t"
  shows "ho_typeof S V (D@B) t=Some A"
  by (rule ho_empty_steps_type[OF ho_instantiate_beta_path[OF instantiated]
    ho_typeof_free_subst_context[OF pattern subst]])

theorem ho_general_step_type:
  assumes step: "ho_step S V R B t u" and ty: "ho_typeof S V B t=Some A"
  shows "ho_typeof S V B u=Some A"
using step ty
proof (induction arbitrary: A rule: ho_step.induct)
  case (rule G l r B s t u)
  obtain T where l: "ho_typeof S G [] (ho_erase_pattern l)=Some T"
    and r: "ho_typeof S G [] (ho_erase_pattern r)=Some T"
    using rule.hyps(2) by (auto simp: ho_rule_welltyped_def split: option.splits)
  have lt: "ho_typeof S V B t=Some T"
    using ho_instantiate_type[OF l rule.hyps(3)] rule.hyps(4) by simp
  have rt: "ho_typeof S V B u=Some T"
    using ho_instantiate_type[OF r rule.hyps(3)] rule.hyps(5) by simp
  show ?case using lt rt rule.prems by simp
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

lemma ho_source_plain_beta_path:
  assumes body: "ho_typeof S V (A#B) t=Some C" and arg: "ho_typeof S V B x=Some A"
    and closed: "ho_interpretation_closed I"
  shows "beta\<^sup>*\<^sup>*
    (App (ho_source_interpretation S V B I e (HAbs A t))
         (ho_source_interpretation S V B I e x))
    (ho_source_interpretation S V B I e (ho_beta_subst x 0 t))"
  using ho_source_abs_path[OF body closed, of e "ho_source_interpretation S V B I e x"]
  by (simp add: ho_source_interpretation_def ho_compile_beta[OF body arg]
    ho_evaluate_beta_subst[OF closed])

lemma ho_typed_fold_head:
  "ho_typeof S V B (foldl HApp t xs)=Some A \<Longrightarrow>
    \<exists>T. ho_typeof S V B t=Some T"
proof (induction xs arbitrary: t)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  have rest: "ho_typeof S V B (foldl HApp (HApp t x) xs)=Some A" using Cons.prems by simp
  obtain T where "ho_typeof S V B (HApp t x)=Some T"
    using Cons.IH[OF rest] by blast
  then show ?case by (auto split: option.splits ho_type.splits if_splits)
qed

lemma ho_typed_fold_arguments:
  "ho_typeof S V B (foldl HApp t xs)=Some A \<Longrightarrow>
    list_all (\<lambda>x. \<exists>T. ho_typeof S V B x=Some T) xs"
proof (induction xs arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have rest: "ho_typeof S V B (foldl HApp (HApp t x) xs)=Some A" using Cons.prems by simp
  obtain T where "ho_typeof S V B (HApp t x)=Some T" using ho_typed_fold_head[OF rest] by blast
  then have "\<exists>T. ho_typeof S V B x=Some T" by (auto split: option.splits ho_type.splits if_splits)
  with Cons.IH[OF rest] show ?case by simp
qed

lemma ho_meta_apply_interpretation_path:
  assumes instantiated: "ho_meta_apply t xs=Some u"
    and ty: "ho_typeof S V B (foldl HApp t xs)=Some A"
    and closed: "ho_interpretation_closed I"
  shows "beta\<^sup>*\<^sup>*
    (foldl App (ho_source_interpretation S V B I e t)
       (map (ho_source_interpretation S V B I e) xs))
    (ho_source_interpretation S V B I e u)"
using instantiated ty
proof (induction xs arbitrary: t u)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain T b where t: "t=HAbs T b"
    and rest: "ho_meta_apply (ho_beta_subst x 0 b) xs=Some u"
    using Cons.prems(1) by (auto split: ho_term.splits)
  have folded: "ho_typeof S V B (foldl HApp (HApp t x) xs)=Some A" using Cons.prems(2) by simp
  obtain C where head: "ho_typeof S V B (HApp t x)=Some C" using ho_typed_fold_head[OF folded] by blast
  then have body: "ho_typeof S V (T#B) b=Some C" and arg: "ho_typeof S V B x=Some T"
    unfolding t by (auto split: option.splits ho_type.splits if_splits)
  have path: "(ho_step S V [] B)\<^sup>*\<^sup>* (foldl HApp (HApp t x) xs)
      (foldl HApp (ho_beta_subst x 0 b) xs)"
    by (rule ho_empty_steps_fold; auto simp: t list_all2_refl intro: ho_step.beta)
  have typed: "ho_typeof S V B (foldl HApp (ho_beta_subst x 0 b) xs)=Some A"
    by (rule ho_empty_steps_type[OF path folded])
  have first: "beta\<^sup>*\<^sup>*
      (App (ho_source_interpretation S V B I e t) (ho_source_interpretation S V B I e x))
      (ho_source_interpretation S V B I e (ho_beta_subst x 0 b))"
    unfolding t by (rule ho_source_plain_beta_path[OF body arg closed])
  have folded_path: "beta\<^sup>*\<^sup>* (foldl App
      (App (ho_source_interpretation S V B I e t) (ho_source_interpretation S V B I e x)) ys)
      (foldl App (ho_source_interpretation S V B I e (ho_beta_subst x 0 b)) ys)" for ys
    using first by (induction ys rule: rev_induct) (auto intro: rtrancl_beta_AppL)
  show ?case using rtranclp_trans[OF folded_path Cons.IH[OF rest typed]] by simp
qed

end
