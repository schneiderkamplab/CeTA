theory Higher_Order_Candidate_Calls
  imports Higher_Order_Candidate_Fundamental
begin

lemma ho_positive_result:
  "ho_positive_type rank n T \<Longrightarrow> rank (ho_result_sort T)\<le>n"
  by (induction T) auto

lemma ho_apply_terms_fold:
  "ho_apply_terms f xs=foldl HApp f xs"
  by (induction xs arbitrary: f) auto

context ho_source_accessible_reducibility
begin

lemma source_candidate_full_application:
  assumes cf: "source.candidate_computable I T f"
    and args: "list_all2 (source.candidate_computable I) (ho_argument_types T) xs"
  shows "source.candidate_computable I (HBase (ho_result_sort T)) (ho_apply_terms f xs)"
  using cf args
proof (induction T arbitrary: f xs)
  case (HBase b)
  then show ?case by simp
next
  case (HArrow A C)
  obtain x ys where xs: "xs=x#ys" and cx: "source.candidate_computable I A x"
    and cy: "list_all2 (source.candidate_computable I) (ho_argument_types C) ys"
    using HArrow.prems(2) by (auto simp: list_all2_Cons1)
  have cf: "source.candidate_computable I C (HApp f x)"
    by (rule source.candidate_application[OF HArrow.prems(1) cx])
  show ?case using HArrow.IH(2)[OF cf cy] xs by simp
qed

lemma source_candidate_slice:
  assumes bases: "\<And>b. b\<in>ho_type_bases T \<Longrightarrow> rank b\<le>n"
  shows "source.candidate_computable
      (access.candidate_slice n (access.candidate_lower n) (access.candidate_level n (access.candidate_lower n))) T t =
    source_candidate T t"
  by (rule source.candidate_agreement) (rule access.candidate_slice_agreement[OF bases], assumption)

lemma source_candidate_extended_SN:
  assumes comp: "source_candidate (HBase b) t" and bound: "rank b\<le>n"
  shows "Wellfounded.accp (\<lambda>u t. ho_step S V R B t u \<or>
    access.accessible_step n (access.candidate_slice n (access.candidate_lower n)
      (access.candidate_level n (access.candidate_lower n))) t u) t"
proof -
  let ?I = "access.candidate_slice n (access.candidate_lower n) (access.candidate_level n (access.candidate_lower n))"
  show ?thesis
  proof (cases "rank b=n")
    case True
    have ct: "access.candidate_level n (access.candidate_lower n) b t"
      using comp access.accessible_candidates_level[OF True, of t] by simp
    show ?thesis using ct
      by (subst (asm) access.candidate_level_unfold) (simp add: access.candidate_operator_def)
  next
    case False
    have sn: "source.strongly_normalizing t" by (rule source.candidate_SN[OF comp])
    have ty: "ho_typeof S V B t=Some (HBase b)" by (rule source.candidate_typed[OF comp])
    show ?thesis using sn ty
    proof (induction t rule: accp.induct)
      case (accI t)
      show ?case
      proof (rule accp.accI)
        fix u assume st: "ho_step S V R B t u \<or> access.accessible_step n ?I t u"
        have step: "ho_step S V R B t u"
          using st accI.prems False by (auto simp: access.accessible_step_def)
        have ut: "ho_typeof S V B u=Some (HBase b)"
          by (rule ho_zero_arity_step_type[OF step zero accI.prems])
        show "Wellfounded.accp (\<lambda>u t. ho_step S V R B t u \<or> access.accessible_step n ?I t u) u"
          by (rule accI.IH[OF step ut])
      qed
    qed
  qed
qed

lemma source_candidate_base_intro:
  assumes ty: "ho_typeof S V B t=Some (HBase b)"
    and reducts: "\<And>u. ho_step S V R B t u \<Longrightarrow> source_candidate (HBase b) u"
    and direct: "\<And>T v. (T,v)\<in>ho_accessible_arguments rank S V B t \<Longrightarrow> source_candidate T v"
  shows "source_candidate (HBase b) t"
proof -
  let ?n = "rank b"
  let ?I = "access.candidate_slice ?n (access.candidate_lower ?n) (access.candidate_level ?n (access.candidate_lower ?n))"
  have red: "access.candidate_level ?n (access.candidate_lower ?n) b u"
    if "ho_step S V R B t u" for u
    using reducts[OF that] access.accessible_candidates_level[of b ?n u] by simp
  have dc: "source.candidate_computable ?I T v"
    if av: "(T,v)\<in>ho_accessible_arguments rank S V B t" for T v
  proof -
    have pos: "ho_positive_type rank ?n T" by (rule access.accessible_positive[OF ty av])
    have bases: "\<And>c. c\<in>ho_type_bases T \<Longrightarrow> rank c\<le>?n"
      using ho_polarity_bases[of rank ?n T] pos by blast
    show ?thesis using source_candidate_slice[where T=T and t=v, OF bases] direct[OF av] by simp
  qed
  have access_sn: "Wellfounded.accp (\<lambda>u t. ho_step S V R B t u \<or> access.accessible_step ?n ?I t u) u"
    if st: "access.accessible_step ?n ?I t u" for u
  proof -
    obtain c T v xs where ct: "ho_typeof S V B t=Some (HBase c)" and rn: "rank c=?n"
      and av: "(T,v)\<in>ho_accessible_arguments rank S V B t"
      and args: "list_all2 (source.candidate_computable ?I) (ho_argument_types T) xs"
      and eq: "u=ho_apply_terms v xs"
      using st unfolding access.accessible_step_def ho_apply_terms_fold by blast
    have cu: "source.candidate_computable ?I (HBase (ho_result_sort T)) u"
      using source_candidate_full_application[OF dc[OF av] args] eq by simp
    have pos: "ho_positive_type rank ?n T" by (rule access.accessible_positive[OF ty av])
    have bound: "rank (ho_result_sort T)\<le>?n" by (rule ho_positive_result[OF pos])
    have global: "source_candidate (HBase (ho_result_sort T)) u"
      using cu source_candidate_slice[where T="HBase (ho_result_sort T)" and n="?n" and t=u] bound by simp
    show ?thesis by (rule source_candidate_extended_SN[OF global bound])
  qed
  have ct: "access.candidate_level ?n (access.candidate_lower ?n) b t"
    by (rule access.candidate_level_intro[OF refl ty red access_sn dc])
  have it: "access.accessible_candidates b t"
    using ct access.accessible_candidates_level[of b ?n t] by simp
  show ?thesis using ty access.accessible_candidates_SN[OF it] it by simp
qed

end

end
