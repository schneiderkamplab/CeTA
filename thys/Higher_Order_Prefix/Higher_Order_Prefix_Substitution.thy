theory Higher_Order_Prefix_Substitution
  imports Higher_Order_Prefix_Calls
begin

definition ho_prefix_subst where
  "ho_prefix_subst G s qs n = (if n<length G then s n else qs!(n-length G))"

definition ho_prefix_variables where
  "ho_prefix_variables G Ds = map HFree [length G..<length G+length Ds]"

lemma ho_typed_subst_agreement:
  assumes ty: "ho_typeof S G B t=Some T"
    and eq: "\<And>n. n<length G \<Longrightarrow> s n=s' n"
  shows "ho_subst s d t=ho_subst s' d t"
  using ty
  by (induction t arbitrary: B T d)
     (auto simp: eq split: option.splits ho_type.splits if_splits)

lemma ho_prefix_subst_old:
  assumes "ho_typeof S G B t=Some T"
  shows "ho_subst (ho_prefix_subst G s qs) d t=ho_subst s d t"
  by (rule ho_typed_subst_agreement[OF assms])
     (simp add: ho_prefix_subst_def)

lemma ho_prefix_variables_typed:
  "list_all2 (\<lambda>A x. ho_typeof S (G@Ds) [] x=Some A) Ds (ho_prefix_variables G Ds)"
proof (rule list_all2_all_nthI)
  show "length Ds=length (ho_prefix_variables G Ds)"
    by (simp add: ho_prefix_variables_def)
  fix i assume i: "i<length Ds"
  show "ho_typeof S (G@Ds) [] (ho_prefix_variables G Ds!i)=Some (Ds!i)"
    using i by (simp add: ho_prefix_variables_def nth_append)
qed

lemma ho_prefix_subst_variables:
  assumes len: "length qs=length Ds"
  shows "map (ho_subst (ho_prefix_subst G s qs) 0) (ho_prefix_variables G Ds)=qs"
proof (rule nth_equalityI)
  show "length (map (ho_subst (ho_prefix_subst G s qs) 0) (ho_prefix_variables G Ds))=length qs"
    using len by (simp add: ho_prefix_variables_def)
  fix i assume "i<length (map (ho_subst (ho_prefix_subst G s qs) 0) (ho_prefix_variables G Ds))"
  then have i: "i<length Ds" by (simp add: ho_prefix_variables_def)
  show "map (ho_subst (ho_prefix_subst G s qs) 0) (ho_prefix_variables G Ds)!i=qs!i"
    using i by (simp add: ho_prefix_variables_def ho_prefix_subst_def)
qed

lemma ho_prefix_subst_typed:
  assumes old: "ho_typed_subst S V B G s"
    and args: "list_all2 (\<lambda>A x. ho_typeof S V B x=Some A) Ds qs"
  shows "ho_typed_subst S V B (G@Ds) (ho_prefix_subst G s qs)"
  unfolding ho_typed_subst_def
proof (intro allI impI)
  fix n assume n: "n<length (G@Ds)"
  show "ho_typeof S V B (ho_prefix_subst G s qs n)=Some ((G@Ds)!n)"
  proof (cases "n<length G")
    case True
    show ?thesis using old True
      by (simp add: ho_typed_subst_def ho_prefix_subst_def nth_append)
  next
    case False
    have idx: "n-length G<length Ds" using n False by simp
    have "ho_typeof S V B (qs!(n-length G))=Some (Ds!(n-length G))"
      using list_all2_nthD[OF args idx] .
    then show ?thesis using False by (simp add: ho_prefix_subst_def nth_append)
  qed
qed

end
