theory Higher_Order_Accessible_Fixpoint
  imports Higher_Order_Candidate_Interpretation
begin

lemma ho_positive_domains:
  "ho_positive_type rank n T \<Longrightarrow>
   list_all (ho_negative_type rank n) (ho_argument_types T)"
  by (induction T) auto

locale ho_accessible_reducibility = ho_reducibility step application typed
  for step :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and application :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and typed :: "ho_type \<Rightarrow> 'a \<Rightarrow> bool" +
  fixes rank :: "nat \<Rightarrow> nat"
    and accessible :: "'a \<Rightarrow> (ho_type \<times> 'a) set"
  assumes accessible_positive:
    "typed (HBase b) t \<Longrightarrow> (T,v)\<in>accessible t \<Longrightarrow> ho_positive_type rank (rank b) T"
begin

definition accessible_step where
  "accessible_step n I t u = (\<exists>b T v xs. typed (HBase b) t \<and> rank b=n \<and>
    (T,v)\<in>accessible t \<and> list_all2 (candidate_computable I) (ho_argument_types T) xs \<and>
    u=foldl application v xs)"

definition candidate_slice where
  "candidate_slice n L X b t = (if rank b<n then L b t else rank b=n \<and> X b t)"

definition candidate_operator where
  "candidate_operator n L X b t = (rank b=n \<and> typed (HBase b) t \<and>
    Wellfounded.accp (\<lambda>u t. step t u \<or> accessible_step n (candidate_slice n L X) t u) t \<and>
    (\<forall>u. step\<^sup>*\<^sup>* t u \<longrightarrow> (\<forall>(T,v)\<in>accessible u. candidate_computable (candidate_slice n L X) T v)))"

lemma typed_reductions:
  "step\<^sup>*\<^sup>* t u \<Longrightarrow> typed A t \<Longrightarrow> typed A u"
  by (induction rule: rtranclp_induct) (auto intro: type_preserved)

lemma accessible_step_antimono:
  assumes inclusion: "\<And>b t. rank b\<le>n \<Longrightarrow> I b t \<Longrightarrow> J b t"
    and agreement: "\<And>b t. rank b<n \<Longrightarrow> J b t \<Longrightarrow> I b t"
    and st: "accessible_step n J t u"
  shows "accessible_step n I t u"
proof -
  obtain b T v xs where ty: "typed (HBase b) t" and rn: "rank b=n"
    and av: "(T,v)\<in>accessible t"
    and args: "list_all2 (candidate_computable J) (ho_argument_types T) xs"
    and eq: "u=foldl application v xs"
    using st unfolding accessible_step_def by blast
  have pos: "ho_positive_type rank n T" using accessible_positive[OF ty av] rn by simp
  have neg: "list_all (ho_negative_type rank n) (ho_argument_types T)"
    by (rule ho_positive_domains[OF pos])
  have ia: "list_all2 (candidate_computable I) (ho_argument_types T) xs"
    using args neg candidate_polarity[where I=I and J=J and rank=rank and n=n, OF inclusion agreement]
    by (induction rule: list_all2_induct) auto
  show ?thesis using ty rn av ia eq unfolding accessible_step_def by blast
qed

lemma candidate_operator_mono: "mono (candidate_operator n L)"
proof (rule monoI)
  fix X Y :: "nat \<Rightarrow> 'a \<Rightarrow> bool" assume xy: "X\<le>Y"
  show "candidate_operator n L X \<le> candidate_operator n L Y"
  proof (intro le_funI)
  fix b t
  show "candidate_operator n L X b t \<le> candidate_operator n L Y b t"
    unfolding le_bool_def
  proof
    assume before: "candidate_operator n L X b t"
    let ?I = "candidate_slice n L X"
    let ?J = "candidate_slice n L Y"
    have inclusion: "rank c\<le>n \<Longrightarrow> ?I c u \<Longrightarrow> ?J c u" for c u
      using xy by (auto simp: candidate_slice_def le_fun_def)
    have agreement: "rank c<n \<Longrightarrow> ?J c u \<Longrightarrow> ?I c u" for c u
      by (simp add: candidate_slice_def)
    have relation: "(\<lambda>u t. step t u \<or> accessible_step n ?J t u) \<le>
        (\<lambda>u t. step t u \<or> accessible_step n ?I t u)"
      using accessible_step_antimono[where n=n and I="?I" and J="?J",
        OF inclusion agreement] by auto
    have rn: "rank b=n" and ty: "typed (HBase b) t"
      and acc: "Wellfounded.accp (\<lambda>u t. step t u \<or> accessible_step n ?I t u) t"
      and inherited: "\<And>u T v. step\<^sup>*\<^sup>* t u \<Longrightarrow> (T,v)\<in>accessible u \<Longrightarrow> candidate_computable ?I T v"
      using before unfolding candidate_operator_def by auto
    have acc': "Wellfounded.accp (\<lambda>u t. step t u \<or> accessible_step n ?J t u) t"
      using accp_subset[OF relation] acc by auto
    have inherited': "candidate_computable ?J T v"
      if steps: "step\<^sup>*\<^sup>* t u" and av: "(T,v)\<in>accessible u" for u T v
    proof -
      have ut: "typed (HBase b) u" by (rule typed_reductions[OF steps ty])
      have pos: "ho_positive_type rank n T" using accessible_positive[OF ut av] rn by simp
      show ?thesis using candidate_polarity[where I="?I" and J="?J" and rank=rank and n=n and A=T,
        OF inclusion agreement] pos inherited[OF steps av] by blast
    qed
    show "candidate_operator n L Y b t"
      using rn ty acc' inherited' unfolding candidate_operator_def by blast
  qed
  qed
qed

definition candidate_level where
  "candidate_level n L = gfp (candidate_operator n L)"

lemma candidate_level_unfold:
  "candidate_level n L = candidate_operator n L (candidate_level n L)"
  unfolding candidate_level_def by (rule gfp_unfold[OF candidate_operator_mono])

lemma candidate_level_typed:
  "candidate_level n L b t \<Longrightarrow> typed (HBase b) t"
  by (subst (asm) candidate_level_unfold) (simp add: candidate_operator_def)

lemma candidate_level_SN:
  assumes ct: "candidate_level n L b t"
  shows "strongly_normalizing t"
proof -
  have acc: "Wellfounded.accp (\<lambda>u t. step t u \<or>
      accessible_step n (candidate_slice n L (candidate_level n L)) t u) t"
    using ct by (subst (asm) candidate_level_unfold) (simp add: candidate_operator_def)
  have sub: "(\<lambda>u t. step t u) \<le>
      (\<lambda>u t. step t u \<or> accessible_step n (candidate_slice n L (candidate_level n L)) t u)" by auto
  show ?thesis using accp_subset[OF sub] acc by auto
qed

lemma candidate_level_reduction:
  assumes ct: "candidate_level n L b t" and st: "step t u"
  shows "candidate_level n L b u"
proof -
  let ?I = "candidate_slice n L (candidate_level n L)"
  have data: "candidate_operator n L (candidate_level n L) b t"
    using ct by (subst (asm) candidate_level_unfold)
  have rn: "rank b=n" and ty: "typed (HBase b) t"
    and acc: "Wellfounded.accp (\<lambda>u t. step t u \<or> accessible_step n ?I t u) t"
    and inherited: "\<And>v T x. step\<^sup>*\<^sup>* t v \<Longrightarrow> (T,x)\<in>accessible v \<Longrightarrow> candidate_computable ?I T x"
    using data by (auto simp: candidate_operator_def)
  have ut: "typed (HBase b) u" by (rule type_preserved[OF ty st])
  have ua: "Wellfounded.accp (\<lambda>u t. step t u \<or> accessible_step n ?I t u) u"
    by (rule accp_downward[OF acc]) (use st in auto)
  have ui: "candidate_computable ?I T x" if steps: "step\<^sup>*\<^sup>* u v" and ax: "(T,x)\<in>accessible v" for v T x
    by (rule inherited[OF converse_rtranclp_into_rtranclp[OF st steps] ax])
  show ?thesis
    by (subst candidate_level_unfold) (use rn ut ua ui in \<open>auto simp: candidate_operator_def\<close>)
qed

lemma candidate_level_accessible:
  assumes ct: "candidate_level n L b t" and av: "(T,v)\<in>accessible t"
  shows "candidate_computable (candidate_slice n L (candidate_level n L)) T v"
  using ct av by (subst (asm) candidate_level_unfold) (auto simp: candidate_operator_def)

lemma candidate_level_intro:
  assumes rn: "rank b=n" and ty: "typed (HBase b) t"
    and reducts: "\<And>u. step t u \<Longrightarrow> candidate_level n L b u"
    and accessible_SN: "\<And>u. accessible_step n (candidate_slice n L (candidate_level n L)) t u \<Longrightarrow>
      Wellfounded.accp (\<lambda>u t. step t u \<or> accessible_step n (candidate_slice n L (candidate_level n L)) t u) u"
    and accessible_comp: "\<And>T v. (T,v)\<in>accessible t \<Longrightarrow>
      candidate_computable (candidate_slice n L (candidate_level n L)) T v"
  shows "candidate_level n L b t"
proof -
  let ?I = "candidate_slice n L (candidate_level n L)"
  have ua: "Wellfounded.accp (\<lambda>u t. step t u \<or> accessible_step n ?I t u) u"
    if st: "step t u" for u
    using reducts[OF st] by (subst (asm) candidate_level_unfold) (simp add: candidate_operator_def)
  have acc: "Wellfounded.accp (\<lambda>u t. step t u \<or> accessible_step n ?I t u) t"
    by (rule accp.accI) (use ua accessible_SN in auto)
  have inherited: "candidate_computable ?I T v"
    if steps: "step\<^sup>*\<^sup>* t u" and av: "(T,v)\<in>accessible u" for u T v
  proof -
    from steps show ?thesis
    proof (cases rule: converse_rtranclpE)
      case base
      then show ?thesis using accessible_comp av by simp
    next
      case (step x)
      have cx: "candidate_level n L b x" by (rule reducts[OF step(1)])
      have cu: "candidate_level n L b u"
        using step(2) cx by (induction rule: rtranclp_induct) (auto intro: candidate_level_reduction)
      show ?thesis by (rule candidate_level_accessible[OF cu av])
    qed
  qed
  show ?thesis
    by (subst candidate_level_unfold) (use rn ty acc inherited in \<open>auto simp: candidate_operator_def\<close>)
qed

lemma candidate_level_neutral:
  assumes rn: "rank b=n" and ty: "typed (HBase b) t"
    and empty: "accessible t={}"
    and reducts: "\<And>u. step t u \<Longrightarrow> candidate_level n L b u"
  shows "candidate_level n L b t"
proof -
  let ?I = "candidate_slice n L (candidate_level n L)"
  have ua: "Wellfounded.accp (\<lambda>u t. step t u \<or> accessible_step n ?I t u) u"
    if st: "step t u" for u
    using reducts[OF st] by (subst (asm) candidate_level_unfold) (simp add: candidate_operator_def)
  have acc: "Wellfounded.accp (\<lambda>u t. step t u \<or> accessible_step n ?I t u) t"
    by (rule accp.accI) (use ua empty in \<open>auto simp: accessible_step_def\<close>)
  have inherited: "candidate_computable ?I T v"
    if steps: "step\<^sup>*\<^sup>* t u" and av: "(T,v)\<in>accessible u" for u T v
  proof -
    from steps show ?thesis
    proof (cases rule: converse_rtranclpE)
      case base
      then show ?thesis using av empty by simp
    next
      case (step x)
      have cx: "candidate_level n L b x" by (rule reducts[OF step(1)])
      have cu: "candidate_level n L b u"
        using step(2) cx by (induction rule: rtranclp_induct) (auto intro: candidate_level_reduction)
      show ?thesis by (rule candidate_level_accessible[OF cu av])
    qed
  qed
  show ?thesis
    by (subst candidate_level_unfold) (use rn ty acc inherited in \<open>auto simp: candidate_operator_def\<close>)
qed

end

end
