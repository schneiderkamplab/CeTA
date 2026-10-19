theory Higher_Order_Accessible_Candidates
  imports Higher_Order_Accessible_Fixpoint
begin

lemma ho_polarity_bases:
  "(ho_positive_type rank n T \<longrightarrow> (\<forall>b\<in>ho_type_bases T. rank b\<le>n)) \<and>
   (ho_negative_type rank n T \<longrightarrow> (\<forall>b\<in>ho_type_bases T. rank b\<le>n))"
  by (induction T) auto

context ho_accessible_reducibility
begin

primrec candidate_stages where
  "candidate_stages 0 = candidate_level 0 (\<lambda>b t. False)"
| "candidate_stages (Suc n) = (\<lambda>b t. if rank b\<le>n then candidate_stages n b t
    else candidate_level (Suc n) (candidate_stages n) b t)"

definition accessible_candidates where
  "accessible_candidates b t = candidate_stages (rank b) b t"

definition candidate_lower where
  "candidate_lower n = (case n of 0 \<Rightarrow> (\<lambda>b t. False) | Suc m \<Rightarrow> candidate_stages m)"

lemma candidate_stages_stable:
  assumes mn: "m\<le>n" and bm: "rank b\<le>m"
  shows "candidate_stages n b t=candidate_stages m b t"
  using mn bm
proof (induction n arbitrary: m)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "m=Suc n")
    case True
    then show ?thesis by simp
  next
    case False
    have mn: "m\<le>n" using Suc.prems(1) False by arith
    have bn: "rank b\<le>n" using mn Suc.prems(2) by arith
    show ?thesis using Suc.IH[OF mn Suc.prems(2)] bn by simp
  qed
qed

lemma candidate_stages_current:
  "rank b=n \<Longrightarrow> candidate_stages n b t=candidate_level n (candidate_lower n) b t"
  by (cases n) (auto simp: candidate_lower_def)

lemma accessible_candidates_level:
  "rank b=n \<Longrightarrow> accessible_candidates b t=candidate_level n (candidate_lower n) b t"
  unfolding accessible_candidates_def by (simp add: candidate_stages_current)

lemma candidate_slice_agreement:
  assumes bn: "rank b\<le>n"
  shows "candidate_slice n (candidate_lower n) (candidate_level n (candidate_lower n)) b t =
    accessible_candidates b t"
proof (cases "rank b=n")
  case True
  then show ?thesis by (simp add: candidate_slice_def accessible_candidates_level)
next
  case False
  have lt: "rank b<n" using bn False by arith
  obtain m where n: "n=Suc m" using lt by (cases n) auto
  have bm: "rank b\<le>m" using lt n by simp
  have stable: "candidate_stages m b t=candidate_stages (rank b) b t"
    by (rule candidate_stages_stable[OF bm]) simp
  show ?thesis using lt n stable
    by (simp add: candidate_slice_def candidate_lower_def accessible_candidates_def)
qed

lemma accessible_candidates_typed:
  assumes ct: "accessible_candidates b t"
  shows "typed (HBase b) t"
proof -
  have "candidate_level (rank b) (candidate_lower (rank b)) b t"
    using ct accessible_candidates_level[of b "rank b" t] by simp
  then show ?thesis by (rule candidate_level_typed)
qed

lemma accessible_candidates_SN:
  assumes ct: "accessible_candidates b t"
  shows "strongly_normalizing t"
proof -
  have "candidate_level (rank b) (candidate_lower (rank b)) b t"
    using ct accessible_candidates_level[of b "rank b" t] by simp
  then show ?thesis by (rule candidate_level_SN)
qed

lemma accessible_candidates_reduction:
  assumes ct: "accessible_candidates b t" and st: "step t u"
  shows "accessible_candidates b u"
proof -
  have old: "candidate_level (rank b) (candidate_lower (rank b)) b t"
    using ct accessible_candidates_level[of b "rank b" t] by simp
  have "candidate_level (rank b) (candidate_lower (rank b)) b u"
    by (rule candidate_level_reduction[OF old st])
  then show ?thesis using accessible_candidates_level[of b "rank b" u] by simp
qed

lemma accessible_candidates_neutral:
  assumes ty: "typed (HBase b) t" and empty: "accessible t={}"
    and reducts: "\<And>u. step t u \<Longrightarrow> accessible_candidates b u"
  shows "accessible_candidates b t"
proof -
  have red: "candidate_level (rank b) (candidate_lower (rank b)) b u"
    if "step t u" for u
    using reducts[OF that] accessible_candidates_level[of b "rank b" u] by simp
  have "candidate_level (rank b) (candidate_lower (rank b)) b t"
    by (rule candidate_level_neutral[OF refl ty empty red])
  then show ?thesis using accessible_candidates_level[of b "rank b" t] by simp
qed

theorem accessible_candidates_accessible:
  assumes ct: "accessible_candidates b t" and av: "(T,v)\<in>accessible t"
  shows "candidate_computable accessible_candidates T v"
proof -
  let ?n = "rank b"
  let ?I = "candidate_slice ?n (candidate_lower ?n) (candidate_level ?n (candidate_lower ?n))"
  have old: "candidate_level ?n (candidate_lower ?n) b t"
    using ct accessible_candidates_level[of b ?n t] by simp
  have comp: "candidate_computable ?I T v" by (rule candidate_level_accessible[OF old av])
  have ty: "typed (HBase b) t" by (rule accessible_candidates_typed[OF ct])
  have pos: "ho_positive_type rank ?n T" by (rule accessible_positive[OF ty av])
  have bases: "\<And>c. c\<in>ho_type_bases T \<Longrightarrow> rank c\<le>?n" using ho_polarity_bases[of rank ?n T] pos by blast
  have eq: "candidate_computable ?I T v=candidate_computable accessible_candidates T v"
    by (rule candidate_agreement) (rule candidate_slice_agreement[OF bases], assumption)
  show ?thesis using comp eq by simp
qed

end

end
