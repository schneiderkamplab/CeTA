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

lemma ho_beta_delete_lift_source:
  "k\<le>d \<Longrightarrow> ho_beta_subst u (k+c) (ho_lift (Suc d) c t)=ho_lift d c t"
proof (induction t arbitrary: c)
  case (HBound n)
  then show ?case by (auto split: if_splits; arith)
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
  have ih: "ho_beta_subst u (k+Suc c) (ho_lift (Suc d) (Suc c) t)=ho_lift d (Suc c) t"
    by (rule HAbs.IH[OF HAbs.prems])
  show ?case using ih by simp
qed

lemma ho_beta_composition_source:
  "i\<le>k \<Longrightarrow>
    ho_beta_subst u k (ho_beta_subst v i t)=
    ho_beta_subst (ho_beta_subst u (k-i) v) i (ho_beta_subst u (Suc k) t)"
proof (induction t arbitrary: i k)
  case (HBound n)
  have lifted: "ho_beta_subst u k (ho_lift i 0 v)=ho_lift i 0 (ho_beta_subst u (k-i) v)"
    using ho_beta_lift_source[where c=0 and k="k-i" and d=i and t=v and u=u] HBound.prems by simp
  have deleted: "ho_beta_subst (ho_beta_subst u (k-i) v) i (ho_lift (Suc k) 0 u)=ho_lift k 0 u"
    using ho_beta_delete_lift_source[OF HBound.prems, where c=0 and t=u] by simp
  show ?case using HBound.prems by (auto simp: lifted deleted split: if_splits; arith)
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
  have le: "Suc i\<le>Suc k" using HAbs.prems by simp
  have ih: "ho_beta_subst u (Suc k) (ho_beta_subst v (Suc i) t)=
    ho_beta_subst (ho_beta_subst u (Suc k-Suc i) v) (Suc i) (ho_beta_subst u (Suc (Suc k)) t)"
    by (rule HAbs.IH[OF le])
  show ?case using ih by simp
qed

theorem ho_source_rule_beta_substitution:
  assumes zero: "ho_zero_arity_rules R" and member: "(G,l,r)\<in>set R"
    and rule_typed: "ho_rule_welltyped S (G,l,r)"
    and subst: "ho_typed_subst S V (D@T#C) G s"
    and lhs: "ho_instantiate s 0 l=Some t" and rhs: "ho_instantiate s 0 r=Some u"
    and arg: "ho_typeof S V C x=Some T"
  shows "ho_step S V R (D@C) (ho_beta_subst x (length D) t) (ho_beta_subst x (length D) u)"
proof -
  let ?s = "\<lambda>n. ho_beta_subst x (length D) (s n)"
  obtain A where lt: "ho_typeof S G [] (ho_erase_pattern l)=Some A"
    and rt: "ho_typeof S G [] (ho_erase_pattern r)=Some A"
    using rule_typed unfolding ho_rule_welltyped_def by (auto split: option.splits)
  have zl: "ho_zero_arity_pattern l" and zr: "ho_zero_arity_pattern r"
    using zero member unfolding ho_zero_arity_rules_def by auto
  have ts: "t=ho_subst s 0 (ho_erase_pattern l)"
    using lhs ho_zero_arity_instantiate[OF zl, of s 0] by simp
  have us: "u=ho_subst s 0 (ho_erase_pattern r)"
    using rhs ho_zero_arity_instantiate[OF zr, of s 0] by simp
  have typed_subst: "ho_typed_subst S V (D@C) G ?s"
  proof (unfold ho_typed_subst_def, intro allI impI)
    fix n assume n: "n<length G"
    have before: "ho_typeof S V (D@T#C) (s n)=Some (G!n)"
      using subst n unfolding ho_typed_subst_def by blast
    show "ho_typeof S V (D@C) (ho_beta_subst x (length D) (s n))=Some (G!n)"
      by (rule ho_typeof_beta_context[OF before arg])
  qed
  have li: "ho_instantiate ?s 0 l=Some (ho_beta_subst x (length D) t)"
    using ho_zero_arity_instantiate[OF zl, of ?s 0] ho_beta_free_rule_source[OF lt, of x "length D" s]
    by (simp add: ts)
  have ri: "ho_instantiate ?s 0 r=Some (ho_beta_subst x (length D) u)"
    using ho_zero_arity_instantiate[OF zr, of ?s 0] ho_beta_free_rule_source[OF rt, of x "length D" s]
    by (simp add: us)
  show ?thesis by (rule ho_step.rule[OF member rule_typed typed_subst li ri])
qed

theorem ho_source_step_beta_substitution:
  assumes step: "ho_step S V R B t u" and zero: "ho_zero_arity_rules R"
    and ctx_eq: "B=D@T#C" and arg: "ho_typeof S V C x=Some T"
  shows "ho_step S V R (D@C) (ho_beta_subst x (length D) t) (ho_beta_subst x (length D) u)"
  using step ctx_eq
proof (induction arbitrary: D rule: ho_step.induct)
  case (rule G l r B s t u)
  show ?case using ho_source_rule_beta_substitution[OF zero rule.hyps(1,2)]
    rule.hyps(3,4,5) rule.prems arg by blast
next
  case (beta B A t u)
  have composition: "ho_beta_subst x (length D) (ho_beta_subst u 0 t)=
    ho_beta_subst (ho_beta_subst x (length D) u) 0 (ho_beta_subst x (Suc (length D)) t)"
    using ho_beta_composition_source[where i=0 and k="length D" and u=x and v=u and t=t] by simp
  show ?case by (simp add: composition ho_step.beta)
next
  case (app_left B t u y)
  then show ?case by (simp add: ho_step.app_left)
next
  case (app_right B t u y)
  then show ?case by (simp add: ho_step.app_right)
next
  case (abs A B t u)
  have ctx: "A#B=(A#D)@T#C" using abs.prems by simp
  have ih: "ho_step S V R ((A#D)@C)
    (ho_beta_subst x (length (A#D)) t) (ho_beta_subst x (length (A#D)) u)"
    by (rule abs.IH[OF ctx])
  show ?case using ho_step.abs[OF ih[simplified]] by simp
qed

lemma ho_lift_commute_source:
  "i\<le>k \<Longrightarrow> ho_lift d (k+e) (ho_lift e i t)=
    ho_lift e i (ho_lift d k t)"
proof (induction t arbitrary: i k)
  case (HBound n)
  then show ?case by (auto split: if_splits; arith)
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
  have le: "Suc i\<le>Suc k" using HAbs.prems by simp
  have ih: "ho_lift d (Suc k+e) (ho_lift e (Suc i) t)=
    ho_lift e (Suc i) (ho_lift d (Suc k) t)"
    by (rule HAbs.IH[OF le])
  show ?case using ih by simp
qed

lemma ho_lift_free_substitution_source:
  "ho_bound_closed e t \<Longrightarrow>
    ho_lift d (k+e) (ho_subst s e t)=
    ho_subst (\<lambda>n. ho_lift d k (s n)) e t"
proof (induction t arbitrary: e)
  case (HBound n)
  then show ?case by simp
next
  case (HFree n)
  show ?case by (simp add: ho_lift_commute_source[where i=0, simplified])
next
  case (HConst n)
  show ?case by simp
next
  case (HApp f x)
  then show ?case by simp
next
  case (HAbs A t)
  have closed: "ho_bound_closed (Suc e) t" using HAbs.prems by simp
  have ih: "ho_lift d (k+Suc e) (ho_subst s (Suc e) t)=
    ho_subst (\<lambda>n. ho_lift d k (s n)) (Suc e) t"
    by (rule HAbs.IH[OF closed])
  show ?case using ih by simp
qed

lemma ho_lift_beta_source:
  "i\<le>k \<Longrightarrow> ho_lift d k (ho_beta_subst u i t)=
    ho_beta_subst (ho_lift d (k-i) u) i (ho_lift d (Suc k) t)"
proof (induction t arbitrary: i k)
  case (HBound n)
  have commute: "ho_lift d k (ho_lift i 0 u)=ho_lift i 0 (ho_lift d (k-i) u)"
    using ho_lift_commute_source[where i=0 and k="k-i" and e=i and t=u and d=d]
      HBound.prems by simp
  show ?case using HBound.prems by (auto simp: commute split: if_splits; arith)
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
  have le: "Suc i\<le>Suc k" using HAbs.prems by simp
  have ih: "ho_lift d (Suc k) (ho_beta_subst u (Suc i) t)=
    ho_beta_subst (ho_lift d (Suc k-Suc i) u) (Suc i) (ho_lift d (Suc (Suc k)) t)"
    by (rule HAbs.IH[OF le])
  show ?case using ih by simp
qed

lemma ho_source_rule_lift:
  assumes zero: "ho_zero_arity_rules R" and member: "(G,l,r)\<in>set R"
    and rt: "ho_rule_welltyped S (G,l,r)"
    and subst: "ho_typed_subst S V (B@C) G s"
    and lhs: "ho_instantiate s 0 l=Some t" and rhs: "ho_instantiate s 0 r=Some u"
  shows "ho_step S V R (B@D@C)
    (ho_lift (length D) (length B) t) (ho_lift (length D) (length B) u)"
proof -
  let ?s = "\<lambda>n. ho_lift (length D) (length B) (s n)"
  obtain A where lt: "ho_typeof S G [] (ho_erase_pattern l)=Some A"
    and rr: "ho_typeof S G [] (ho_erase_pattern r)=Some A"
    using rt unfolding ho_rule_welltyped_def by (auto split: option.splits)
  have zl: "ho_zero_arity_pattern l" and zr: "ho_zero_arity_pattern r"
    using zero member unfolding ho_zero_arity_rules_def by auto
  have lc: "ho_bound_closed 0 (ho_erase_pattern l)"
    and rc: "ho_bound_closed 0 (ho_erase_pattern r)"
    using ho_typeof_bound_closed[OF lt] ho_typeof_bound_closed[OF rr] by simp_all
  have ts: "t=ho_subst s 0 (ho_erase_pattern l)"
    using lhs ho_zero_arity_instantiate[OF zl, of s 0] by simp
  have us: "u=ho_subst s 0 (ho_erase_pattern r)"
    using rhs ho_zero_arity_instantiate[OF zr, of s 0] by simp
  have typed_subst: "ho_typed_subst S V (B@D@C) G ?s"
    using subst ho_typeof_lift_context[where S=S and V=V and B=B and C=C and D=D]
    unfolding ho_typed_subst_def by blast
  have li: "ho_instantiate ?s 0 l=Some (ho_lift (length D) (length B) t)"
    using ho_zero_arity_instantiate[OF zl, of ?s 0]
      ho_lift_free_substitution_source[OF lc, of "length D" "length B" s]
    by (simp add: ts)
  have ri: "ho_instantiate ?s 0 r=Some (ho_lift (length D) (length B) u)"
    using ho_zero_arity_instantiate[OF zr, of ?s 0]
      ho_lift_free_substitution_source[OF rc, of "length D" "length B" s]
    by (simp add: us)
  show ?thesis by (rule ho_step.rule[OF member rt typed_subst li ri])
qed

theorem ho_source_step_lift:
  assumes step: "ho_step S V R E t u" and zero: "ho_zero_arity_rules R"
    and ctx_eq: "E=B@C"
  shows "ho_step S V R (B@D@C)
    (ho_lift (length D) (length B) t) (ho_lift (length D) (length B) u)"
  using step ctx_eq
proof (induction arbitrary: B rule: ho_step.induct)
  case (rule G l r E s t u)
  show ?case using ho_source_rule_lift[OF zero rule.hyps(1,2)]
    rule.hyps(3,4,5) rule.prems by blast
next
  case (beta E A t u)
  have commute: "ho_lift (length D) (length B) (ho_beta_subst u 0 t)=
    ho_beta_subst (ho_lift (length D) (length B) u) 0
      (ho_lift (length D) (Suc (length B)) t)"
    using ho_lift_beta_source[where i=0 and k="length B" and d="length D" and u=u and t=t] by simp
  show ?case by (simp add: commute ho_step.beta)
next
  case (app_left E t u y)
  then show ?case by (simp add: ho_step.app_left)
next
  case (app_right E t u y)
  then show ?case by (simp add: ho_step.app_right)
next
  case (abs A E t u)
  have ctx: "A#E=(A#B)@C" using abs.prems by simp
  have ih: "ho_step S V R ((A#B)@D@C)
    (ho_lift (length D) (length (A#B)) t) (ho_lift (length D) (length (A#B)) u)"
    by (rule abs.IH[OF ctx])
  show ?case using ho_step.abs[OF ih[simplified]] by simp
qed

lemma ho_source_steps_app_left:
  "(ho_step S V R B)\<^sup>*\<^sup>* t u \<Longrightarrow>
    (ho_step S V R B)\<^sup>*\<^sup>* (HApp t x) (HApp u x)"
  by (induction rule: rtranclp_induct)
    (auto intro: rtranclp.rtrancl_into_rtrancl ho_step.app_left)

lemma ho_source_steps_app_right:
  "(ho_step S V R B)\<^sup>*\<^sup>* t u \<Longrightarrow>
    (ho_step S V R B)\<^sup>*\<^sup>* (HApp x t) (HApp x u)"
  by (induction rule: rtranclp_induct)
    (auto intro: rtranclp.rtrancl_into_rtrancl ho_step.app_right)

lemma ho_source_steps_abs:
  "(ho_step S V R (A#B))\<^sup>*\<^sup>* t u \<Longrightarrow>
    (ho_step S V R B)\<^sup>*\<^sup>* (HAbs A t) (HAbs A u)"
  by (induction rule: rtranclp_induct)
    (auto intro: rtranclp.rtrancl_into_rtrancl ho_step.abs)

theorem ho_source_beta_argument_steps:
  assumes step: "ho_step S V R C u v" and zero: "ho_zero_arity_rules R"
  shows "(ho_step S V R (B@C))\<^sup>*\<^sup>*
    (ho_beta_subst u (length B) t) (ho_beta_subst v (length B) t)"
proof (induction t arbitrary: B)
  case (HBound n)
  have lifted: "ho_step S V R (B@C) (ho_lift (length B) 0 u) (ho_lift (length B) 0 v)"
    using ho_source_step_lift[OF step zero, where B="[]" and D=B] by simp
  show ?case using lifted by (auto split: if_splits)
next
  case (HFree n)
  show ?case by simp
next
  case (HConst n)
  show ?case by simp
next
  case (HApp f x)
  have left: "(ho_step S V R (B@C))\<^sup>*\<^sup>*
    (HApp (ho_beta_subst u (length B) f) (ho_beta_subst u (length B) x))
    (HApp (ho_beta_subst v (length B) f) (ho_beta_subst u (length B) x))"
    by (rule ho_source_steps_app_left[OF HApp.IH(1)])
  have right: "(ho_step S V R (B@C))\<^sup>*\<^sup>*
    (HApp (ho_beta_subst v (length B) f) (ho_beta_subst u (length B) x))
    (HApp (ho_beta_subst v (length B) f) (ho_beta_subst v (length B) x))"
    by (rule ho_source_steps_app_right[OF HApp.IH(2)])
  show ?case using rtranclp_trans[OF left right] by simp
next
  case (HAbs A t)
  have ih: "(ho_step S V R (A#(B@C)))\<^sup>*\<^sup>*
    (ho_beta_subst u (Suc (length B)) t) (ho_beta_subst v (Suc (length B)) t)"
    using HAbs.IH[where B="A#B"] by simp
  show ?case using ho_source_steps_abs[OF ih] by simp
qed

corollary ho_source_steps_beta_substitution:
  assumes steps: "(ho_step S V R (D@T#C))\<^sup>*\<^sup>* t u"
    and zero: "ho_zero_arity_rules R" and arg: "ho_typeof S V C x=Some T"
  shows "(ho_step S V R (D@C))\<^sup>*\<^sup>*
    (ho_beta_subst x (length D) t) (ho_beta_subst x (length D) u)"
  using steps
proof (induction rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  have next_step: "ho_step S V R (D@C)
    (ho_beta_subst x (length D) y) (ho_beta_subst x (length D) z)"
    by (rule ho_source_step_beta_substitution[OF step.hyps(2) zero refl arg])
  show ?case using step.IH next_step by (rule rtranclp.rtrancl_into_rtrancl)
qed

end
