theory Higher_Order_Source_Fundamental
  imports Higher_Order_Source_Beta
begin

text \<open>Simultaneous substitution of free variables and the outer bound
context. The depth counts binders retained in the output; all supplied images
live in the target context and are lifted when entering an abstraction.\<close>

fun ho_open :: "(nat \<Rightarrow> ho_term) \<Rightarrow> (nat \<Rightarrow> ho_term)
    \<Rightarrow> nat \<Rightarrow> ho_term \<Rightarrow> ho_term" where
  "ho_open s b d (HBound n) = (if n<d then HBound n else ho_lift d 0 (b (n-d)))"
| "ho_open s b d (HFree n) = ho_lift d 0 (s n)"
| "ho_open s b d (HConst n) = HConst n"
| "ho_open s b d (HApp f x) = HApp (ho_open s b d f) (ho_open s b d x)"
| "ho_open s b d (HAbs A t) = HAbs A (ho_open s b (Suc d) t)"

lemma ho_open_beta:
  "ho_beta_subst x d (ho_open s b (Suc d) t)=
    ho_open s (\<lambda>n. if n=0 then x else b (n-1)) d t"
proof (induction t arbitrary: d)
  case (HBound n)
  have deleted: "ho_beta_subst x d (ho_lift (Suc d) 0 (b (n-Suc d)))=
    ho_lift d 0 (b (n-Suc d))"
    using ho_beta_delete_lift_source[where k=d and d=d and c=0 and u=x and t="b (n-Suc d)"] by simp
  show ?case by (auto simp: deleted split: if_splits; arith)
next
  case (HFree n)
  show ?case using ho_beta_delete_lift_source[where k=d and d=d and c=0 and u=x and t="s n"] by simp
next
  case (HConst n)
  show ?case by simp
next
  case (HApp f x)
  then show ?case by simp
next
  case (HAbs A t)
  then show ?case by simp
qed

lemma ho_open_type:
  assumes ty: "ho_typeof S G (D@E) t=Some A"
    and free: "\<And>n. n<length G \<Longrightarrow> ho_typeof S V B (s n)=Some (G!n)"
    and bound: "\<And>n. n<length E \<Longrightarrow> ho_typeof S V B (b n)=Some (E!n)"
  shows "ho_typeof S V (D@B) (ho_open s b (length D) t)=Some A"
  using ty
proof (induction t arbitrary: D A)
  case (HBound n)
  show ?case
  proof (cases "n<length D")
    case True
    then show ?thesis using HBound.prems by (simp add: nth_append)
  next
    case False
    have n: "n-length D<length E" and eq: "E!(n-length D)=A"
      using HBound.prems False by (auto simp: nth_append split: if_splits)
    have lifted: "ho_typeof S V (D@B) (ho_lift (length D) 0 (b (n-length D)))=Some A"
      using ho_typeof_lift_context[where B="[]" and D=D, simplified, OF bound[OF n]] eq by simp
    show ?thesis using False lifted by simp
  qed
next
  case (HFree n)
  have n: "n<length G" and eq: "G!n=A" using HFree.prems by (auto split: if_splits)
  show ?case using ho_typeof_lift_context[where B="[]" and D=D, simplified, OF free[OF n]] eq by simp
next
  case (HConst n)
  then show ?case by simp
next
  case (HApp f x)
  then show ?case by (auto split: option.splits ho_type.splits if_splits)
next
  case (HAbs T t)
  obtain C where bt: "ho_typeof S G ((T#D)@E) t=Some C" and eq: "A=HArrow T C"
    using HAbs.prems by (auto split: option.splits)
  show ?case using HAbs.IH[OF bt] eq by simp
qed

lemma ho_open_identity: "ho_open HFree HBound d t=t"
  by (induction t arbitrary: d) auto

lemma ho_open_closed:
  "ho_bound_closed d t \<Longrightarrow> ho_open s b d t=ho_subst s d t"
  by (induction t arbitrary: d) auto

fun ho_type_bases where
  "ho_type_bases (HBase b)={b}"
| "ho_type_bases (HArrow A C)=ho_type_bases A \<union> ho_type_bases C"

fun ho_binder_types where
  "ho_binder_types (HApp f x)=ho_binder_types f \<union> ho_binder_types x"
| "ho_binder_types (HAbs A t)=insert A (ho_binder_types t)"
| "ho_binder_types t={}"

context ho_source_neutral_reducibility
begin

lemma source_type_inhabited:
  "(\<And>b. b\<in>ho_type_bases A \<Longrightarrow> \<exists>x. source.computable (HBase b) x)
    \<Longrightarrow> \<exists>x. source.computable A x"
proof (induction A)
  case (HBase b)
  then show ?case by simp
next
  case (HArrow A C)
  obtain a where ca: "source.computable A a" using HArrow.IH(1) HArrow.prems by auto
  obtain c where cc: "source.computable C c" using HArrow.IH(2) HArrow.prems by auto
  have ct: "ho_typeof S V B c=Some C" by (rule source.computable_typed[OF cc])
  have lifted: "ho_typeof S V (A#B) (ho_lift 1 0 c)=Some C"
    using ho_typeof_lift_context[where B="[]" and D="[A]", simplified, OF ct] by simp
  have ty: "ho_typeof S V B (HAbs A (ho_lift 1 0 c))=Some (HArrow A C)" using lifted by simp
  have instances: "source.computable C (ho_beta_subst x 0 (ho_lift 1 0 c))" for x
    using ho_beta_delete_lift_source[where k=0 and d=0 and c=0 and u=x and t=c] cc by simp
  have "source.computable (HArrow A C) (HAbs A (ho_lift 1 0 c))"
    by (rule source_computable_abstraction_from_instances[OF ty ca]) (rule instances)
  then show ?case by blast
qed

theorem source_fundamental:
  assumes ty: "ho_typeof S G E t=Some A"
    and free: "\<And>n. n<length G \<Longrightarrow> source.computable (G!n) (s n)"
    and bound: "\<And>n. n<length E \<Longrightarrow> source.computable (E!n) (b n)"
    and symbols: "\<And>n T. ho_lookup S n=Some T \<Longrightarrow> source.computable T (HConst n)"
    and inhabited: "\<And>T. T\<in>ho_binder_types t \<Longrightarrow> \<exists>x. source.computable T x"
  shows "source.computable A (ho_open s b 0 t)"
  using ty bound inhabited
proof (induction t arbitrary: E b A)
  case (HBound n)
  then show ?case by (auto split: if_splits)
next
  case (HFree n)
  then show ?case using free by (auto split: if_splits)
next
  case (HConst n)
  then show ?case using symbols by simp
next
  case (HApp f x)
  obtain T where ft: "ho_typeof S G E f=Some (HArrow T A)" and xt: "ho_typeof S G E x=Some T"
    using HApp.prems(1) by (auto split: option.splits ho_type.splits if_splits)
  have cf: "source.computable (HArrow T A) (ho_open s b 0 f)"
    by (rule HApp.IH(1)[OF ft HApp.prems(2)]) (use HApp.prems(3) in auto)
  have cx: "source.computable T (ho_open s b 0 x)"
    by (rule HApp.IH(2)[OF xt HApp.prems(2)]) (use HApp.prems(3) in auto)
  show ?case using source.computable_application[OF cf cx] by simp
next
  case (HAbs T t)
  obtain C where bt: "ho_typeof S G (T#E) t=Some C" and eq: "A=HArrow T C"
    using HAbs.prems(1) by (auto split: option.splits)
  obtain a where ca: "source.computable T a" using HAbs.prems(3) by auto
  have ot: "ho_typeof S V B (HAbs T (ho_open s b 1 t))=Some (HArrow T C)"
    using ho_open_type[where D="[]", simplified, OF HAbs.prems(1)
      source.computable_typed[OF free] source.computable_typed[OF HAbs.prems(2)]] eq by simp
  have instances: "source.computable C (ho_beta_subst x 0 (ho_open s b 1 t))"
    if cx: "source.computable T x" for x
  proof -
    let ?b = "\<lambda>n. if n=0 then x else b (n-1)"
    have env: "source.computable ((T#E)!n) (?b n)" if n: "n<length (T#E)" for n
      using n cx HAbs.prems(2) by (cases n) auto
    have "source.computable C (ho_open s ?b 0 t)"
      by (rule HAbs.IH[OF bt env]) (use HAbs.prems(3) in auto)
    then show ?thesis by (simp add: ho_open_beta)
  qed
  show ?case using source_computable_abstraction_from_instances[OF ot ca instances] eq by simp
qed

corollary source_constants_suffice:
  assumes ty: "ho_typeof S V B t=Some A"
    and symbols: "\<And>n T. ho_lookup S n=Some T \<Longrightarrow> source.computable T (HConst n)"
    and inhabited: "\<And>T. T\<in>ho_binder_types t \<Longrightarrow> \<exists>x. source.computable T x"
  shows "source.computable A t"
proof -
  have fv: "source.computable (V!n) (HFree n)" if "n<length V" for n
    by (rule source_free_computable) (simp add: that)
  have bv: "source.computable (B!n) (HBound n)" if "n<length B" for n
    by (rule source_bound_computable) (simp add: that)
  show ?thesis using source_fundamental[OF ty fv bv symbols inhabited] by (simp add: ho_open_identity)
qed

end

end
