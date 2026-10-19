theory Higher_Order_Candidate_Interpretation
  imports "Higher_Order_Priority.Higher_Order_Priority_Schema"
begin

text \<open>Candidate-parametric computability for typed accessibility. This
  theory does not add an executable acceptance rule. The positivity conditions
  follow Fuhs and Kop, ESOP 2019, Definition 72 and Lemma 73
  (extended version, arXiv:1902.06733).\<close>

fun ho_positive_type :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ho_type \<Rightarrow> bool"
  and ho_negative_type :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ho_type \<Rightarrow> bool" where
  "ho_positive_type rank n (HBase b) = (rank b\<le>n)"
| "ho_positive_type rank n (HArrow A B) =
    (ho_negative_type rank n A \<and> ho_positive_type rank n B)"
| "ho_negative_type rank n (HBase b) = (rank b<n)"
| "ho_negative_type rank n (HArrow A B) =
    (ho_positive_type rank n A \<and> ho_negative_type rank n B)"

context ho_reducibility
begin

fun candidate_computable where
  "candidate_computable I (HBase b) t =
    (typed (HBase b) t \<and> strongly_normalizing t \<and> I b t)"
| "candidate_computable I (HArrow A B) t =
    (typed (HArrow A B) t \<and> strongly_normalizing t \<and>
     (\<forall>x. candidate_computable I A x \<longrightarrow> candidate_computable I B (application t x)))"

lemma candidate_typed:
  "candidate_computable I A t \<Longrightarrow> typed A t"
  by (cases A) auto

lemma candidate_SN:
  "candidate_computable I A t \<Longrightarrow> strongly_normalizing t"
  by (cases A) auto

lemma candidate_application:
  "candidate_computable I (HArrow A B) f \<Longrightarrow> candidate_computable I A x \<Longrightarrow>
   candidate_computable I B (application f x)"
  by simp

lemma candidate_polarity:
  assumes inclusion: "\<And>b t. rank b\<le>n \<Longrightarrow> I b t \<Longrightarrow> J b t"
    and agreement: "\<And>b t. rank b<n \<Longrightarrow> J b t \<Longrightarrow> I b t"
  shows "(ho_positive_type rank n A \<longrightarrow>
      (\<forall>t. candidate_computable I A t \<longrightarrow> candidate_computable J A t)) \<and>
    (ho_negative_type rank n A \<longrightarrow>
      (\<forall>t. candidate_computable J A t \<longrightarrow> candidate_computable I A t))"
  by (induction A) (auto intro: inclusion agreement)

lemma candidate_reduction:
  assumes closed: "\<And>b t u. I b t \<Longrightarrow> step t u \<Longrightarrow> I b u"
    and comp: "candidate_computable I A t" and st: "step t u"
  shows "candidate_computable I A u"
  using comp st
proof (induction A arbitrary: t u)
  case (HBase b)
  have ty: "typed (HBase b) u" using HBase.prems type_preserved by auto
  have sn: "strongly_normalizing u"
    by (rule accp_downward[OF candidate_SN[OF HBase.prems(1)] HBase.prems(2)])
  show ?case using ty sn HBase.prems closed by auto
next
  case (HArrow A B)
  have ty: "typed (HArrow A B) u" using HArrow.prems type_preserved by auto
  have sn: "strongly_normalizing u"
    by (rule accp_downward[OF candidate_SN[OF HArrow.prems(1)] HArrow.prems(2)])
  have result: "candidate_computable I B (application u x)"
    if cx: "candidate_computable I A x" for x
  proof -
    have ct: "candidate_computable I B (application t x)"
      by (rule candidate_application[OF HArrow.prems(1) cx])
    show ?thesis by (rule HArrow.IH(2)[OF ct application_left[OF HArrow.prems(2)]])
  qed
  show ?case using ty sn result by simp
qed

lemma candidate_reductions:
  assumes closed: "\<And>b t u. I b t \<Longrightarrow> step t u \<Longrightarrow> I b u"
    and steps: "step\<^sup>*\<^sup>* t u" and comp: "candidate_computable I A t"
  shows "candidate_computable I A u"
  using steps comp by (induction rule: rtranclp_induct) (auto intro: candidate_reduction[OF closed])

lemma candidate_agreement:
  assumes equal: "\<And>b t. b\<in>ho_type_bases A \<Longrightarrow> I b t=J b t"
  shows "candidate_computable I A t=candidate_computable J A t"
  using equal by (induction A arbitrary: t) auto

end

end
