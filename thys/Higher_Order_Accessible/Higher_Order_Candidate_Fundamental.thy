theory Higher_Order_Candidate_Fundamental
  imports Higher_Order_Candidate_Beta
begin

context ho_source_accessible_reducibility
begin

lemma source_candidate_type_inhabited:
  "(\<And>b. b\<in>ho_type_bases A \<Longrightarrow> \<exists>x. source_candidate (HBase b) x)
    \<Longrightarrow> \<exists>x. source_candidate A x"
proof (induction A)
  case (HBase b)
  then show ?case by simp
next
  case (HArrow A C)
  obtain a where ca: "source_candidate A a" using HArrow.IH(1) HArrow.prems by auto
  obtain c where cc: "source_candidate C c" using HArrow.IH(2) HArrow.prems by auto
  have ct: "ho_typeof S V B c=Some C" by (rule source.candidate_typed[OF cc])
  have lifted: "ho_typeof S V (A#B) (ho_lift 1 0 c)=Some C"
    using ho_typeof_lift_context[where B="[]" and D="[A]", simplified, OF ct] by simp
  have ty: "ho_typeof S V B (HAbs A (ho_lift 1 0 c))=Some (HArrow A C)" using lifted by simp
  have instances: "source_candidate C (ho_beta_subst x 0 (ho_lift 1 0 c))" for x
    using ho_beta_delete_lift_source[where k=0 and d=0 and c=0 and u=x and t=c] cc by simp
  have "source_candidate (HArrow A C) (HAbs A (ho_lift 1 0 c))"
    by (rule source_candidate_abstraction_from_instances[OF ty ca]) (rule instances)
  then show ?case by blast
qed

theorem source_candidate_fundamental:
  assumes ty: "ho_typeof S G E t=Some A"
    and free: "\<And>n. n<length G \<Longrightarrow> source_candidate (G!n) (s n)"
    and bound: "\<And>n. n<length E \<Longrightarrow> source_candidate (E!n) (b n)"
    and symbols: "\<And>n T. ho_lookup S n=Some T \<Longrightarrow> source_candidate T (HConst n)"
    and inhabited: "\<And>T. T\<in>ho_binder_types t \<Longrightarrow> \<exists>x. source_candidate T x"
  shows "source_candidate A (ho_open s b 0 t)"
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
  have cf: "source_candidate (HArrow T A) (ho_open s b 0 f)"
    by (rule HApp.IH(1)[OF ft HApp.prems(2)]) (use HApp.prems(3) in auto)
  have cx: "source_candidate T (ho_open s b 0 x)"
    by (rule HApp.IH(2)[OF xt HApp.prems(2)]) (use HApp.prems(3) in auto)
  show ?case using source.candidate_application[OF cf cx] by simp
next
  case (HAbs T t)
  obtain C where bt: "ho_typeof S G (T#E) t=Some C" and eq: "A=HArrow T C"
    using HAbs.prems(1) by (auto split: option.splits)
  obtain a where ca: "source_candidate T a" using HAbs.prems(3) by auto
  have ot: "ho_typeof S V B (HAbs T (ho_open s b 1 t))=Some (HArrow T C)"
    using ho_open_type[where D="[]", simplified, OF HAbs.prems(1)
      source.candidate_typed[OF free] source.candidate_typed[OF HAbs.prems(2)]] eq by simp
  have instances: "source_candidate C (ho_beta_subst x 0 (ho_open s b 1 t))"
    if cx: "source_candidate T x" for x
  proof -
    let ?b = "\<lambda>n. if n=0 then x else b (n-1)"
    have env: "source_candidate ((T#E)!n) (?b n)" if n: "n<length (T#E)" for n
      using n cx HAbs.prems(2) by (cases n) auto
    have "source_candidate C (ho_open s ?b 0 t)"
      by (rule HAbs.IH[OF bt env]) (use HAbs.prems(3) in auto)
    then show ?thesis by (simp add: ho_open_beta)
  qed
  show ?case using source_candidate_abstraction_from_instances[OF ot ca instances] eq by simp
qed

corollary source_candidate_constants_suffice:
  assumes ty: "ho_typeof S V B t=Some A"
    and symbols: "\<And>n T. ho_lookup S n=Some T \<Longrightarrow> source_candidate T (HConst n)"
    and inhabited: "\<And>T. T\<in>ho_binder_types t \<Longrightarrow> \<exists>x. source_candidate T x"
  shows "source_candidate A t"
proof -
  have fv: "source_candidate (V!n) (HFree n)" if "n<length V" for n
    by (rule source_candidate_free) (simp add: that)
  have bv: "source_candidate (B!n) (HBound n)" if "n<length B" for n
    by (rule source_candidate_bound) (simp add: that)
  show ?thesis using source_candidate_fundamental[OF ty fv bv symbols inhabited] by (simp add: ho_open_identity)
qed

end

end
