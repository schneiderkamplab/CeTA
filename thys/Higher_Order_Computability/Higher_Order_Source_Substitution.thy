theory Higher_Order_Source_Substitution
  imports Higher_Order_Source_Computability
begin

lemma ho_lift_zero_source [simp]: "ho_lift 0 k t=t"
  by (induction t arbitrary: k) auto

lemma ho_lift_merge_source:
  "c\<le>e \<Longrightarrow> ho_lift d (k+c) (ho_lift e k t)=ho_lift (d+e) k t"
proof (induction t arbitrary: k)
  case (HBound n)
  then show ?case by (auto simp: algebra_simps)
next
  case (HFree n)
  show ?case by simp
next
  case (HConst n)
  show ?case by simp
next
  case (HApp f x)
  then show ?case by simp
next
  case (HAbs A t)
  have ih: "ho_lift d (Suc k+c) (ho_lift e (Suc k) t)=ho_lift (d+e) (Suc k) t"
    by (rule HAbs.IH[OF HAbs.prems])
  show ?case using ih by simp
qed

lemma ho_beta_lift_source:
  "c\<le>k \<Longrightarrow> ho_beta_subst u (k+d) (ho_lift d c t)=
    ho_lift d c (ho_beta_subst u k t)"
proof (induction t arbitrary: c k)
  case (HBound n)
  have merge: "ho_lift d c (ho_lift k 0 u)=ho_lift (k+d) 0 u"
    using ho_lift_merge_source[OF HBound.prems, where k=0 and d=d and t=u] by (simp add: add.commute)
  show ?case using HBound.prems by (auto simp: merge split: if_splits; arith)
next
  case (HFree n)
  then show ?case by simp
next
  case (HConst n)
  then show ?case by simp
next
  case (HApp f x)
  then show ?case by simp
next
  case (HAbs A t)
  have le: "Suc c\<le>Suc k" using HAbs.prems by simp
  have ih: "ho_beta_subst u (Suc k+d) (ho_lift d (Suc c) t)=
    ho_lift d (Suc c) (ho_beta_subst u (Suc k) t)" by (rule HAbs.IH[OF le])
  show ?case using ih by simp
qed

fun ho_bound_closed where
  "ho_bound_closed d (HBound n) = (n<d)"
| "ho_bound_closed d (HFree n) = True"
| "ho_bound_closed d (HConst n) = True"
| "ho_bound_closed d (HApp f x) = (ho_bound_closed d f \<and> ho_bound_closed d x)"
| "ho_bound_closed d (HAbs A t) = ho_bound_closed (Suc d) t"

lemma ho_beta_free_substitution_source:
  "ho_bound_closed d t \<Longrightarrow>
    ho_beta_subst u (k+d) (ho_subst s d t)=
    ho_subst (\<lambda>n. ho_beta_subst u k (s n)) d t"
proof (induction t arbitrary: d)
  case (HBound n)
  then show ?case by simp
next
  case (HFree n)
  show ?case by (simp add: ho_beta_lift_source[where c=0, simplified])
next
  case (HConst n)
  show ?case by simp
next
  case (HApp f x)
  then show ?case by simp
next
  case (HAbs A t)
  have closed: "ho_bound_closed (Suc d) t" using HAbs.prems by simp
  have ih: "ho_beta_subst u (k+Suc d) (ho_subst s (Suc d) t)=
    ho_subst (\<lambda>n. ho_beta_subst u k (s n)) (Suc d) t"
    by (rule HAbs.IH[OF closed])
  show ?case using ih by simp
qed

lemma ho_typeof_bound_closed:
  "ho_typeof S V B t=Some A \<Longrightarrow> ho_bound_closed (length B) t"
proof (induction t arbitrary: B A)
  case (HBound n)
  then show ?case by (auto split: if_splits)
next
  case (HFree n)
  show ?case by simp
next
  case (HConst n)
  show ?case by simp
next
  case (HApp f x)
  then show ?case by (auto split: option.splits ho_type.splits if_splits)
next
  case (HAbs T t)
  obtain C where ty: "ho_typeof S V (T#B) t=Some C" using HAbs.prems by (auto split: option.splits)
  show ?case using HAbs.IH[OF ty] by simp
qed

lemma ho_beta_free_rule_source:
  "ho_typeof S G [] t=Some A \<Longrightarrow>
    ho_beta_subst u k (ho_subst s 0 t)=ho_subst (\<lambda>n. ho_beta_subst u k (s n)) 0 t"
  using ho_beta_free_substitution_source[where d=0, simplified]
    ho_typeof_bound_closed[where B="[]", simplified] by blast

end
