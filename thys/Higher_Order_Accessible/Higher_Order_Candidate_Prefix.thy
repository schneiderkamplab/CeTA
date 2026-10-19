theory Higher_Order_Candidate_Prefix
  imports Higher_Order_Candidate_Saturated
begin

context ho_source_accessible_reducibility
begin

theorem candidate_from_prefix_calls:
  assumes ty: "ho_typeof S V B f=Some A"
    and bound: "n\<le>length (ho_argument_types A)"
    and inhabited: "\<And>b. b\<in>ho_type_bases A \<Longrightarrow> \<exists>x. source_candidate (HBase b) x"
    and calls: "\<And>xs. list_all2 source_candidate (take n (ho_argument_types A)) xs \<Longrightarrow>
      source_candidate (ho_drop_type n A) (ho_apply_terms f xs)"
  shows "source_candidate A f"
  using ty bound inhabited calls
proof (induction n arbitrary: A f)
  case 0
  then show ?case using 0(4)[of "[]"] by simp
next
  case (Suc n)
  obtain T C where eq: "A=HArrow T C" using Suc.prems(2) by (cases A) auto
  have applied: "source_candidate C (HApp f x)" if cx: "source_candidate T x" for x
  proof (rule Suc.IH)
    show "ho_typeof S V B (HApp f x)=Some C" using Suc.prems(1) source.candidate_typed[OF cx] eq by simp
    show "n\<le>length (ho_argument_types C)" using Suc.prems(2) eq by simp
    show "\<exists>x. source_candidate (HBase b) x" if "b\<in>ho_type_bases C" for b
      using Suc.prems(3) that eq by simp
    fix xs assume args: "list_all2 source_candidate (take n (ho_argument_types C)) xs"
    have full: "list_all2 source_candidate (take (Suc n) (ho_argument_types A)) (x#xs)"
      using cx args eq by simp
    show "source_candidate (ho_drop_type n C) (ho_apply_terms (HApp f x) xs)"
      using Suc.prems(4)[OF full] eq by simp
  qed
  obtain a where ca: "source_candidate T a"
    using source_candidate_type_inhabited[where A=T] Suc.prems(3) eq by auto
  have sn: "source.strongly_normalizing f"
    by (rule source_SN_function[OF source.candidate_SN[OF applied[OF ca]]])
  show ?case using Suc.prems(1) sn applied eq by simp
qed

end

end
