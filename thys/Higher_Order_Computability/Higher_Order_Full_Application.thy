theory Higher_Order_Full_Application
  imports Higher_Order_Symbol_Criterion
begin

fun ho_argument_types where
  "ho_argument_types (HBase b)=[]"
| "ho_argument_types (HArrow A C)=A#ho_argument_types C"

fun ho_result_sort where
  "ho_result_sort (HBase b)=b"
| "ho_result_sort (HArrow A C)=ho_result_sort C"

fun ho_drop_type where
  "ho_drop_type 0 A=A"
| "ho_drop_type (Suc n) (HBase b)=HBase b"
| "ho_drop_type (Suc n) (HArrow A C)=ho_drop_type n C"

lemma ho_drop_full_type [simp]:
  "ho_drop_type (length (ho_argument_types A)) A=HBase (ho_result_sort A)"
  by (induction A) auto

definition ho_apply_terms where
  "ho_apply_terms f xs=foldl HApp f xs"

lemma ho_apply_terms_Nil [simp]: "ho_apply_terms f []=f"
  by (simp add: ho_apply_terms_def)

lemma ho_apply_terms_Cons [simp]: "ho_apply_terms f (x#xs)=ho_apply_terms (HApp f x) xs"
  by (simp add: ho_apply_terms_def)

lemma ho_apply_terms_append [simp]:
  "ho_apply_terms f (xs@ys)=ho_apply_terms (ho_apply_terms f xs) ys"
  by (simp add: ho_apply_terms_def foldl_append)

context ho_source_neutral_reducibility
begin

lemma source_SN_function:
  "source.strongly_normalizing (HApp f x) \<Longrightarrow> source.strongly_normalizing f"
proof -
  have reflection: "source.strongly_normalizing f" if sn: "source.strongly_normalizing t" and eq: "t=HApp f x" for t f
    using sn eq
  proof (induction t arbitrary: f rule: accp.induct)
    case (accI t)
    show ?case
    proof (rule accp.accI)
      fix g assume fg: "ho_step S V R B f g"
      have "ho_step S V R B t (HApp g x)" using ho_step.app_left[OF fg] accI.prems by simp
      then show "source.strongly_normalizing g" by (rule accI.IH[OF _ refl])
    qed
  qed
  assume "source.strongly_normalizing (HApp f x)"
  then show ?thesis by (rule reflection[OF _ refl])
qed

fun full_computable where
  "full_computable (HBase b) t = source.computable (HBase b) t"
| "full_computable (HArrow A C) t = (ho_typeof S V B t=Some (HArrow A C) \<and>
    (\<forall>x. source.computable A x \<longrightarrow> full_computable C (HApp t x)))"

theorem full_computable_imp_computable:
  "full_computable A t \<Longrightarrow>
    (\<And>b. b\<in>ho_type_bases A \<Longrightarrow> \<exists>x. source.computable (HBase b) x) \<Longrightarrow>
    source.computable A t"
proof (induction A arbitrary: t)
  case (HBase b)
  then show ?case by simp
next
  case (HArrow A C)
  have applied: "source.computable C (HApp t x)" if cx: "source.computable A x" for x
  proof (rule HArrow.IH(2))
    show "full_computable C (HApp t x)" using HArrow.prems(1) cx by simp
    show "\<exists>x. source.computable (HBase b) x" if "b\<in>ho_type_bases C" for b
      using HArrow.prems(2) that by simp
  qed
  obtain a where ca: "source.computable A a"
    using source_type_inhabited[where A=A] HArrow.prems(2) by auto
  have sn: "source.strongly_normalizing t"
    by (rule source_SN_function[OF source.computable_SN[OF applied[OF ca]]])
  show ?case using HArrow.prems(1) sn applied by simp
qed

theorem full_computable_from_base_calls:
  assumes ty: "ho_typeof S V B f=Some A"
    and calls: "\<And>xs. list_all2 source.computable (ho_argument_types A) xs \<Longrightarrow>
      source.computable (HBase (ho_result_sort A)) (ho_apply_terms f xs)"
  shows "full_computable A f"
  using ty calls
proof (induction A arbitrary: f)
  case (HBase b)
  have "source.computable (HBase b) (ho_apply_terms f [])"
    using HBase.prems(2)[of "[]"] by simp
  then show ?case by simp
next
  case (HArrow A C)
  have applied: "full_computable C (HApp f x)" if cx: "source.computable A x" for x
  proof (rule HArrow.IH(2))
    show "ho_typeof S V B (HApp f x)=Some C"
      using HArrow.prems(1) source.computable_typed[OF cx] by simp
    fix xs assume args: "list_all2 source.computable (ho_argument_types C) xs"
    have full: "list_all2 source.computable (ho_argument_types (HArrow A C)) (x#xs)"
      using cx args by simp
    show "source.computable (HBase (ho_result_sort C)) (ho_apply_terms (HApp f x) xs)"
      using HArrow.prems(2)[OF full] by simp
  qed
  show ?case using HArrow.prems(1) applied by simp
qed

corollary computable_from_base_calls:
  assumes ty: "ho_typeof S V B f=Some A"
    and inhabited: "\<And>b. b\<in>ho_type_bases A \<Longrightarrow> \<exists>x. source.computable (HBase b) x"
    and calls: "\<And>xs. list_all2 source.computable (ho_argument_types A) xs \<Longrightarrow>
      source.computable (HBase (ho_result_sort A)) (ho_apply_terms f xs)"
  shows "source.computable A f"
  by (rule full_computable_imp_computable[OF full_computable_from_base_calls[OF ty calls] inhabited])

theorem computable_from_prefix_calls:
  assumes ty: "ho_typeof S V B f=Some A"
    and bound: "n\<le>length (ho_argument_types A)"
    and inhabited: "\<And>b. b\<in>ho_type_bases A \<Longrightarrow> \<exists>x. source.computable (HBase b) x"
    and calls: "\<And>xs. list_all2 source.computable (take n (ho_argument_types A)) xs \<Longrightarrow>
      source.computable (ho_drop_type n A) (ho_apply_terms f xs)"
  shows "source.computable A f"
  using ty bound inhabited calls
proof (induction n arbitrary: A f)
  case 0
  then show ?case using 0(4)[of "[]"] by simp
next
  case (Suc n)
  obtain T C where eq: "A=HArrow T C" using Suc.prems(2) by (cases A) auto
  have applied: "source.computable C (HApp f x)" if cx: "source.computable T x" for x
  proof (rule Suc.IH)
    show "ho_typeof S V B (HApp f x)=Some C" using Suc.prems(1) source.computable_typed[OF cx] eq by simp
    show "n\<le>length (ho_argument_types C)" using Suc.prems(2) eq by simp
    show "\<exists>x. source.computable (HBase b) x" if "b\<in>ho_type_bases C" for b
      using Suc.prems(3) that eq by simp
    fix xs assume args: "list_all2 source.computable (take n (ho_argument_types C)) xs"
    have full: "list_all2 source.computable (take (Suc n) (ho_argument_types A)) (x#xs)"
      using cx args eq by simp
    show "source.computable (ho_drop_type n C) (ho_apply_terms (HApp f x) xs)"
      using Suc.prems(4)[OF full] eq by simp
  qed
  obtain a where ca: "source.computable T a"
    using source_type_inhabited[where A=T] Suc.prems(3) eq by auto
  have sn: "source.strongly_normalizing f"
    by (rule source_SN_function[OF source.computable_SN[OF applied[OF ca]]])
  show ?case using Suc.prems(1) sn applied eq by simp
qed

end

end
