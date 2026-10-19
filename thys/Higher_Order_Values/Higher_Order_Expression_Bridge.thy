theory Higher_Order_Expression_Bridge
  imports Higher_Order_Interpretation
begin

text \<open>Type annotations are reconstructed from the original typed input.
Free rule variables become environment entries after the local binders; they
are not turned into constants or erased. Ill-typed terms have no semantic
claim: the correctness theorem below requires the original type judgement.\<close>

fun ho_compile where
  "ho_compile S V B (HBound n) = HEVar n"
| "ho_compile S V B (HFree n) = HEVar (length B+n)"
| "ho_compile S V B (HConst n) = HEConst n"
| "ho_compile S V B (HApp f x) = (case ho_typeof S V B f of
    Some (HArrow A C) \<Rightarrow> HEApp A C (ho_compile S V B f) (ho_compile S V B x)
    | _ \<Rightarrow> HEVar 0)"
| "ho_compile S V B (HAbs A t) = (case ho_typeof S V (A#B) t of
    Some C \<Rightarrow> HEAbs A C (ho_compile S V (A#B) t) | _ \<Rightarrow> HEVar 0)"

theorem ho_compile_type:
  "ho_typeof S V B t=Some A \<Longrightarrow> ho_expression_type S (B@V) (ho_compile S V B t) A"
proof (induction t arbitrary: B A)
  case (HBound n)
  then have n: "n<length B" and a: "A=B!n" by (auto split: if_splits)
  have "ho_expression_type S (B@V) (HEVar n) ((B@V)!n)"
    by (rule ho_expression_type.var) (use n in simp)
  then show ?case using n a by (simp add: nth_append)
next
  case (HFree n)
  then have n: "n<length V" and a: "A=V!n" by (auto split: if_splits)
  have "ho_expression_type S (B@V) (HEVar (length B+n)) ((B@V)!(length B+n))"
    by (rule ho_expression_type.var) (use n in simp)
  then show ?case using a by (simp add: nth_append)
next
  case (HConst n)
  then show ?case by (auto intro: ho_expression_type.const split: if_splits)
next
  case (HApp f x)
  obtain T where f: "ho_typeof S V B f=Some (HArrow T A)"
    and x: "ho_typeof S V B x=Some T"
    using HApp.prems by (auto split: option.splits ho_type.splits if_splits)
  show ?case using ho_expression_type.app[OF HApp.IH(1)[OF f] HApp.IH(2)[OF x]]
    by (simp add: f)
next
  case (HAbs T t)
  obtain C where t: "ho_typeof S V (T#B) t=Some C" and a: "A=HArrow T C"
    using HAbs.prems by (auto split: option.splits)
  have body: "ho_expression_type S (T#(B@V)) (ho_compile S V (T#B) t) C"
    using HAbs.IH[OF t] by simp
  show ?case using ho_expression_type.abs[OF body] by (simp add: t a)
qed

definition ho_source_interpretation where
  "ho_source_interpretation S V B I e t = ho_evaluate I e (ho_compile S V B t)"

theorem ho_source_interpretation_value:
  assumes "ho_typeof S V B t=Some A" "ho_interpretation_closed I"
    "ho_env_value S I" "ho_env_value (B@V) e"
  shows "ho_value A (ho_source_interpretation S V B I e t)"
  unfolding ho_source_interpretation_def
  by (rule ho_evaluate_fundamental[OF ho_compile_type[OF assms(1)] assms(2,3),
    THEN conjunct1, rule_format, OF assms(4)])

lemma ho_typeof_lift_context:
  "ho_typeof S V (B@C) t=Some A \<Longrightarrow>
    ho_typeof S V (B@D@C) (ho_lift (length D) (length B) t)=Some A"
proof (induction t arbitrary: B A)
  case (HBound n)
  then show ?case by (auto simp: nth_append split: if_splits)
next
  case (HFree n)
  then show ?case by simp
next
  case (HConst n)
  then show ?case by simp
next
  case (HApp f x)
  then show ?case by (auto split: option.splits ho_type.splits if_splits)
next
  case (HAbs T t)
  obtain U where ty: "ho_typeof S V ((T#B)@C) t=Some U" and a: "A=HArrow T U"
    using HAbs.prems by (auto split: option.splits)
  from HAbs.IH[OF ty] show ?case by (simp add: a)
qed

lemma ho_expr_rename_comp:
  "ho_expr_rename r (ho_expr_rename s t) = ho_expr_rename (\<lambda>n. r (s n)) t"
proof (induction t arbitrary: r s)
  case (HEAbs A B t)
  have eq: "(\<lambda>n. ho_rename_up r (ho_rename_up s n)) = ho_rename_up (\<lambda>n. r (s n))"
  proof (rule ext)
    fix n show "ho_rename_up r (ho_rename_up s n) = ho_rename_up (\<lambda>n. r (s n)) n"
      by (cases n) (simp_all add: ho_rename_up_def)
  qed
  show ?case by (simp add: HEAbs.IH eq)
qed simp_all

lemma ho_compile_lift_context:
  "ho_typeof S V (B@C) t=Some A \<Longrightarrow>
    ho_compile S V (B@D@C) (ho_lift (length D) (length B) t) =
    ho_expr_rename (\<lambda>n. if n<length B then n else n+length D) (ho_compile S V (B@C) t)"
proof (induction t arbitrary: B A)
  case (HBound n)
  then show ?case by simp
next
  case (HFree n)
  then show ?case by (simp add: add.assoc add.commute add.left_commute)
next
  case (HConst n)
  then show ?case by simp
next
  case (HApp f x)
  obtain T where f: "ho_typeof S V (B@C) f=Some (HArrow T A)"
    and x: "ho_typeof S V (B@C) x=Some T"
    using HApp.prems by (auto split: option.splits ho_type.splits if_splits)
  show ?case by (simp add: f ho_typeof_lift_context[OF f] HApp.IH(1)[OF f] HApp.IH(2)[OF x])
next
  case (HAbs T t)
  obtain U where ty: "ho_typeof S V ((T#B)@C) t=Some U" and a: "A=HArrow T U"
    using HAbs.prems by (auto split: option.splits)
  have up: "ho_rename_up (\<lambda>n. if n<length B then n else n+length D) =
      (\<lambda>n. if n<length (T#B) then n else n+length D)"
  proof (rule ext)
    fix n show "ho_rename_up (\<lambda>n. if n<length B then n else n+length D) n =
      (if n<length (T#B) then n else n+length D)"
      by (cases n) (simp_all add: ho_rename_up_def)
  qed
  show ?case using HAbs.IH[OF ty] ho_typeof_lift_context[OF ty, where D=D]
    by (simp add: ty[simplified] up)
qed

lemma ho_typeof_beta_context:
  "ho_typeof S V (B@T#C) t=Some A \<Longrightarrow> ho_typeof S V C u=Some T \<Longrightarrow>
    ho_typeof S V (B@C) (ho_beta_subst u (length B) t)=Some A"
proof (induction t arbitrary: B A)
  case (HBound n)
  have lifted: "ho_typeof S V (B@C) (ho_lift (length B) 0 u)=Some T"
    using ho_typeof_lift_context[where B="[]" and D=B, simplified, OF HBound.prems(2)] by simp
  have idx: "n-Suc (length B)=k" if "n-length B=Suc k" for k
    using that by arith
  show ?case using HBound.prems(1) lifted
    by (auto simp: nth_append nth_Cons split: if_splits nat.splits; metis idx)
next
  case (HFree n)
  then show ?case by simp
next
  case (HConst n)
  then show ?case by simp
next
  case (HApp f x)
  then show ?case by (auto split: option.splits ho_type.splits if_splits)
next
  case (HAbs U t)
  obtain W where ty: "ho_typeof S V ((U#B)@T#C) t=Some W" and a: "A=HArrow U W"
    using HAbs.prems(1) by (auto split: option.splits)
  from HAbs.IH[OF ty HAbs.prems(2)] show ?case by (simp add: a)
qed

definition ho_expr_subst_at where
  "ho_expr_subst_at k x n = (if n<k then HEVar n
    else if n=k then ho_expr_rename (\<lambda>i. i+k) x else HEVar (n-1))"

lemma ho_expr_subst_at_up:
  "ho_expr_subst_up (ho_expr_subst_at k x) = ho_expr_subst_at (Suc k) x"
proof (rule ext)
  fix n
  show "ho_expr_subst_up (ho_expr_subst_at k x) n = ho_expr_subst_at (Suc k) x n"
    by (cases n) (auto simp: ho_expr_subst_up_def ho_expr_subst_at_def ho_expr_rename_comp)
qed

lemma ho_compile_beta_context:
  "ho_typeof S V (B@T#C) t=Some A \<Longrightarrow> ho_typeof S V C u=Some T \<Longrightarrow>
    ho_compile S V (B@C) (ho_beta_subst u (length B) t) =
    ho_expr_subst (ho_expr_subst_at (length B) (ho_compile S V C u)) (ho_compile S V (B@T#C) t)"
proof (induction t arbitrary: B A)
  case (HBound n)
  have lifted: "ho_compile S V (B@C) (ho_lift (length B) 0 u) =
      ho_expr_rename (\<lambda>i. i+length B) (ho_compile S V C u)"
    using ho_compile_lift_context[where B="[]" and D=B, simplified, OF HBound.prems(2)] by simp
  show ?case by (simp add: ho_expr_subst_at_def lifted)
next
  case (HFree n)
  then show ?case by (simp add: ho_expr_subst_at_def)
next
  case (HConst n)
  then show ?case by simp
next
  case (HApp f x)
  obtain U where f: "ho_typeof S V (B@T#C) f=Some (HArrow U A)"
    and x: "ho_typeof S V (B@T#C) x=Some U"
    using HApp.prems(1) by (auto split: option.splits ho_type.splits if_splits)
  show ?case by (simp add: f ho_typeof_beta_context[OF f HApp.prems(2)]
    HApp.IH(1)[OF f HApp.prems(2)] HApp.IH(2)[OF x HApp.prems(2)])
next
  case (HAbs U t)
  obtain W where ty: "ho_typeof S V ((U#B)@T#C) t=Some W" and a: "A=HArrow U W"
    using HAbs.prems(1) by (auto split: option.splits)
  show ?case using HAbs.IH[OF ty HAbs.prems(2)] ho_typeof_beta_context[OF ty HAbs.prems(2)]
    by (simp add: ty[simplified] ho_expr_subst_at_up)
qed

lemma ho_typeof_free_subst_context:
  "ho_typeof S G B t=Some A \<Longrightarrow> ho_typed_subst S V D G s \<Longrightarrow>
    ho_typeof S V (B@D) (ho_subst s (length B) t)=Some A"
proof (induction t arbitrary: B A)
  case (HBound n)
  then show ?case by (auto simp: nth_append split: if_splits)
next
  case (HFree n)
  then have n: "n<length G" and a: "A=G!n" by (auto split: if_splits)
  have ty: "ho_typeof S V D (s n)=Some A" using HFree.prems(2) n a
    by (simp add: ho_typed_subst_def)
  show ?case using ho_typeof_lift_context[where B="[]" and D=B, simplified, OF ty] by simp
next
  case (HConst n)
  then show ?case by simp
next
  case (HApp f x)
  then show ?case by (auto split: option.splits ho_type.splits if_splits)
next
  case (HAbs T t)
  obtain U where ty: "ho_typeof S G (T#B) t=Some U" and a: "A=HArrow T U"
    using HAbs.prems(1) by (auto split: option.splits)
  from HAbs.IH[OF ty HAbs.prems(2)] show ?case by (simp add: a)
qed

definition ho_expr_free_subst where
  "ho_expr_free_subst k s n = (if n<k then HEVar n else ho_expr_rename (\<lambda>i. i+k) (s (n-k)))"

lemma ho_expr_free_subst_up:
  "ho_expr_subst_up (ho_expr_free_subst k s) = ho_expr_free_subst (Suc k) s"
proof (rule ext)
  fix n
  show "ho_expr_subst_up (ho_expr_free_subst k s) n = ho_expr_free_subst (Suc k) s n"
    by (cases n) (auto simp: ho_expr_subst_up_def ho_expr_free_subst_def ho_expr_rename_comp)
qed

lemma ho_compile_free_subst_context:
  "ho_typeof S G B t=Some A \<Longrightarrow> ho_typed_subst S V D G s \<Longrightarrow>
    ho_compile S V (B@D) (ho_subst s (length B) t) =
    ho_expr_subst (ho_expr_free_subst (length B) (\<lambda>n. ho_compile S V D (s n))) (ho_compile S G B t)"
proof (induction t arbitrary: B A)
  case (HBound n)
  then have "n<length B" by (auto split: if_splits)
  then show ?case by (simp add: ho_expr_free_subst_def)
next
  case (HFree n)
  then have n: "n<length G" and a: "A=G!n" by (auto split: if_splits)
  have ty: "ho_typeof S V D (s n)=Some A" using HFree.prems(2) n a
    by (simp add: ho_typed_subst_def)
  have lifted: "ho_compile S V (B@D) (ho_lift (length B) 0 (s n)) =
      ho_expr_rename (\<lambda>i. i+length B) (ho_compile S V D (s n))"
    using ho_compile_lift_context[where B="[]" and D=B, simplified, OF ty] by simp
  show ?case by (simp add: ho_expr_free_subst_def lifted)
next
  case (HConst n)
  then show ?case by simp
next
  case (HApp f x)
  obtain T where f: "ho_typeof S G B f=Some (HArrow T A)"
    and x: "ho_typeof S G B x=Some T"
    using HApp.prems(1) by (auto split: option.splits ho_type.splits if_splits)
  show ?case by (simp add: f ho_typeof_free_subst_context[OF f HApp.prems(2)]
    HApp.IH(1)[OF f HApp.prems(2)] HApp.IH(2)[OF x HApp.prems(2)])
next
  case (HAbs T t)
  obtain U where ty: "ho_typeof S G (T#B) t=Some U" and a: "A=HArrow T U"
    using HAbs.prems(1) by (auto split: option.splits)
  show ?case using HAbs.IH[OF ty HAbs.prems(2)] ho_typeof_free_subst_context[OF ty HAbs.prems(2)]
    by (simp add: ty ho_expr_free_subst_up)
qed

lemma ho_expr_rename_identity [simp]: "ho_expr_rename (\<lambda>n. n) t=t"
proof (induction t)
  case (HEAbs A B t)
  have up: "ho_rename_up (\<lambda>n. n)=(\<lambda>n. n)"
    by (rule ext; rename_tac n; case_tac n) (simp_all add: ho_rename_up_def)
  show ?case by (simp add: up HEAbs.IH)
qed simp_all

lemma ho_compile_beta:
  assumes "ho_typeof S V (A#B) t=Some C" "ho_typeof S V B x=Some A"
  shows "ho_compile S V B (ho_beta_subst x 0 t) =
    ho_expr_beta_subst (ho_compile S V B x) (ho_compile S V (A#B) t)"
proof -
  have env: "ho_expr_subst_at 0 (ho_compile S V B x) =
    (\<lambda>n. case n of 0 \<Rightarrow> ho_compile S V B x | Suc k \<Rightarrow> HEVar k)"
    by (rule ext; rename_tac n; case_tac n) (simp_all add: ho_expr_subst_at_def)
  show ?thesis using ho_compile_beta_context[where B="[]", simplified, OF assms]
    by (simp add: env ho_expr_beta_subst_def)
qed

lemma ho_compile_free_subst:
  assumes "ho_typeof S G [] t=Some A" "ho_typed_subst S V B G s"
  shows "ho_compile S V B (ho_subst s 0 t) =
    ho_expr_subst (\<lambda>n. ho_compile S V B (s n)) (ho_compile S G [] t)"
proof -
  have zero: "ho_expr_free_subst 0 q=q" for q
    by (rule ext) (simp add: ho_expr_free_subst_def)
  show ?thesis using ho_compile_free_subst_context[where B="[]", simplified, OF assms]
    by (simp add: zero)
qed

end
