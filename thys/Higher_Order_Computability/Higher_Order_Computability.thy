theory Higher_Order_Computability
  imports "Higher_Order_Values.Higher_Order_Source_Order"
begin

text \<open>Abstract typed reducibility candidates for subsequent higher-order
path-order and dependency-pair processors. This is a foundation only: no
executable checker acceptance is added by these conditional results. The
source relation must separately discharge type preservation and application
compatibility. Strong normalization is included at every type.\<close>

locale ho_reducibility =
  fixes step :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and application :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and typed :: "ho_type \<Rightarrow> 'a \<Rightarrow> bool"
  assumes type_preserved: "typed A t \<Longrightarrow> step t u \<Longrightarrow> typed A u"
    and application_type: "typed (HArrow A B) f \<Longrightarrow> typed A x \<Longrightarrow> typed B (application f x)"
    and application_left: "step f g \<Longrightarrow> step (application f x) (application g x)"
    and application_right: "step x y \<Longrightarrow> step (application f x) (application f y)"
begin

abbreviation strongly_normalizing where
  "strongly_normalizing t \<equiv> Wellfounded.accp (\<lambda>u t. step t u) t"

fun computable where
  "computable (HBase b) t = (typed (HBase b) t \<and> strongly_normalizing t)"
| "computable (HArrow A B) t = (typed (HArrow A B) t \<and> strongly_normalizing t \<and>
    (\<forall>x. computable A x \<longrightarrow> computable B (application t x)))"

lemma computable_typed: "computable A t \<Longrightarrow> typed A t"
  by (cases A) auto

lemma computable_SN: "computable A t \<Longrightarrow> strongly_normalizing t"
  by (cases A) auto

lemma computable_application:
  "computable (HArrow A B) f \<Longrightarrow> computable A x \<Longrightarrow> computable B (application f x)"
  by simp

theorem computable_reduction:
  "computable A t \<Longrightarrow> step t u \<Longrightarrow> computable A u"
proof (induction A arbitrary: t u)
  case (HBase b)
  have ty: "typed (HBase b) u" using HBase.prems type_preserved by auto
  have sn: "strongly_normalizing u" using computable_SN[OF HBase.prems(1)] HBase.prems(2)
    by (rule accp_downward)
  show ?case using ty sn by simp
next
  case (HArrow A B)
  have ty: "typed (HArrow A B) u" using HArrow.prems type_preserved by auto
  have sn: "strongly_normalizing u" using computable_SN[OF HArrow.prems(1)] HArrow.prems(2)
    by (rule accp_downward)
  have result: "computable B (application u x)" if x: "computable A x" for x
  proof -
    have before: "computable B (application t x)" by (rule computable_application[OF HArrow.prems(1) x])
    show ?thesis by (rule HArrow.IH(2)[OF before application_left[OF HArrow.prems(2)]])
  qed
  show ?case using ty sn result by simp
qed

theorem computable_reductions:
  "step\<^sup>*\<^sup>* t u \<Longrightarrow> computable A t \<Longrightarrow> computable A u"
  by (induction rule: rtranclp_induct) (auto intro: computable_reduction)

theorem computability_implies_termination:
  assumes all_terms: "\<And>t. typed A t \<Longrightarrow> computable A t"
  shows "wfp (\<lambda>u t. typed A t \<and> step t u)"
proof (rule accp_wfpI, intro allI)
  fix t
  show "Wellfounded.accp (\<lambda>u t. typed A t \<and> step t u) t"
  proof (cases "typed A t")
    case True
    have sn: "strongly_normalizing t" by (rule computable_SN[OF all_terms[OF True]])
    have subset: "(\<lambda>u t. typed A t \<and> step t u) \<le> (\<lambda>u t. step t u)" by auto
    show ?thesis using accp_subset[OF subset] sn by auto
  next
    case False
    show ?thesis by (rule accp.accI) (use False in auto)
  qed
qed

end

locale ho_neutral_reducibility = ho_reducibility step application typed
  for step :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and application :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and typed :: "ho_type \<Rightarrow> 'a \<Rightarrow> bool" +
  fixes neutral :: "'a \<Rightarrow> bool"
  assumes neutral_application: "neutral f \<Longrightarrow> neutral (application f x)"
    and neutral_reduct: "neutral f \<Longrightarrow> step (application f x) u \<Longrightarrow>
      (\<exists>g. step f g \<and> u=application g x) \<or> (\<exists>y. step x y \<and> u=application f y)"
begin

theorem neutral_computable:
  "typed A t \<Longrightarrow> neutral t \<Longrightarrow>
    (\<And>u. step t u \<Longrightarrow> computable A u) \<Longrightarrow> computable A t"
proof (induction A arbitrary: t)
  case (HBase b)
  have sn: "strongly_normalizing t"
  proof (rule accp.accI)
    fix u assume "step t u"
    then show "strongly_normalizing u" by (rule HBase.prems(3)[THEN computable_SN])
  qed
  show ?case using HBase.prems(1) sn by simp
next
  case (HArrow A B)
  have sn: "strongly_normalizing t"
  proof (rule accp.accI)
    fix u assume "step t u"
    then show "strongly_normalizing u" by (rule HArrow.prems(3)[THEN computable_SN])
  qed
  have applied: "computable B (application t x)" if cx: "computable A x" for x
  proof -
    from computable_SN[OF cx] cx show ?thesis
    proof (induction x rule: accp.induct)
      case (accI x)
      have ty: "typed B (application t x)"
        by (rule application_type[OF HArrow.prems(1) computable_typed[OF accI.prems]])
      have neu: "neutral (application t x)" by (rule neutral_application[OF HArrow.prems(2)])
      have reducts: "computable B u" if reduction: "step (application t x) u" for u
      proof -
        from neutral_reduct[OF HArrow.prems(2) reduction] show ?thesis
        proof
          assume "\<exists>g. step t g \<and> u=application g x"
          then obtain g where tg: "step t g" and u: "u=application g x" by auto
          show ?thesis unfolding u by (rule computable_application[OF HArrow.prems(3)[OF tg] accI.prems])
        next
          assume "\<exists>y. step x y \<and> u=application t y"
          then obtain y where xy: "step x y" and u: "u=application t y" by auto
          have cy: "computable A y" by (rule computable_reduction[OF accI.prems xy])
          show ?thesis unfolding u by (rule accI.IH[OF xy cy])
        qed
      qed
      show ?case by (rule HArrow.IH(2)[OF ty neu reducts])
    qed
  qed
  show ?case using HArrow.prems(1) sn applied by simp
qed

end

locale ho_beta_reducibility = ho_neutral_reducibility step application typed neutral
  for step :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and application :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and typed :: "ho_type \<Rightarrow> 'a \<Rightarrow> bool"
    and neutral :: "'a \<Rightarrow> bool" +
  fixes abstraction :: "ho_type \<Rightarrow> 'a \<Rightarrow> 'a"
    and instantiate :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes abstraction_step: "step t u \<Longrightarrow> step (abstraction A t) (abstraction A u)"
    and abstraction_reduct: "step (abstraction A t) u \<Longrightarrow> \<exists>s. step t s \<and> u=abstraction A s"
    and beta_neutral: "neutral (application (abstraction A t) u)"
    and beta_reduct: "step (application (abstraction A t) u) v \<Longrightarrow>
      v=instantiate t u \<or>
      (\<exists>s. step t s \<and> v=application (abstraction A s) u) \<or>
      (\<exists>w. step u w \<and> v=application (abstraction A t) w)"
    and instantiate_left: "step t s \<Longrightarrow> step\<^sup>*\<^sup>* (instantiate t u) (instantiate s u)"
    and instantiate_right: "step u w \<Longrightarrow> step\<^sup>*\<^sup>* (instantiate t u) (instantiate t w)"
begin

theorem computable_beta_expansion:
  assumes st: "strongly_normalizing t" and su: "strongly_normalizing u"
    and ty: "typed B (application (abstraction A t) u)"
    and body: "computable B (instantiate t u)"
  shows "computable B (application (abstraction A t) u)"
using st su ty body
proof (induction t arbitrary: u rule: accp.induct)
  case (accI t)
  note outer = accI.IH
  from accI.prems show ?case
  proof (induction u rule: accp.induct)
    case (accI u)
    have reducts: "computable B v" if reduction: "step (application (abstraction A t) u) v" for v
    proof -
      have vt: "typed B v" by (rule type_preserved[OF accI.prems(1) reduction])
      from beta_reduct[OF reduction] show ?thesis
      proof (elim disjE exE conjE)
        assume "v=instantiate t u"
        then show ?thesis using accI.prems(2) by simp
      next
        fix s assume ts: "step t s" and v: "v=application (abstraction A s) u"
        have snu: "strongly_normalizing u" by (rule accp.accI[OF accI.hyps])
        have cb: "computable B (instantiate s u)"
          by (rule computable_reductions[OF instantiate_left[OF ts] accI.prems(2)])
        show ?thesis using outer[OF ts snu] vt cb unfolding v by blast
      next
        fix w assume uw: "step u w" and v: "v=application (abstraction A t) w"
        have cb: "computable B (instantiate t w)"
          by (rule computable_reductions[OF instantiate_right[OF uw] accI.prems(2)])
        show ?thesis using accI.IH[OF uw] vt cb unfolding v by blast
      qed
    qed
    show ?case by (rule neutral_computable[OF accI.prems(1) beta_neutral reducts])
  qed
qed

lemma abstraction_SN:
  "strongly_normalizing t \<Longrightarrow> strongly_normalizing (abstraction A t)"
proof (induction t rule: accp.induct)
  case (accI t)
  show ?case
  proof (rule accp.accI)
    fix u assume "step (abstraction A t) u"
    then obtain s where "step t s" and "u=abstraction A s" using abstraction_reduct by blast
    then show "strongly_normalizing u" using accI.IH by blast
  qed
qed

theorem computable_abstraction:
  assumes ty: "typed (HArrow A B) (abstraction A t)"
    and sn: "strongly_normalizing t"
    and instances: "\<And>x. computable A x \<Longrightarrow> computable B (instantiate t x)"
  shows "computable (HArrow A B) (abstraction A t)"
proof -
  have applied: "computable B (application (abstraction A t) x)" if cx: "computable A x" for x
    by (rule computable_beta_expansion[OF sn computable_SN[OF cx]
      application_type[OF ty computable_typed[OF cx]] instances[OF cx]])
  show ?thesis using ty abstraction_SN[OF sn] applied by simp
qed

end

end
