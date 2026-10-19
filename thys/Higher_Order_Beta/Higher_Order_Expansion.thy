theory Higher_Order_Expansion
  imports Higher_Order_Beta_Bridge
begin

text \<open>Typed constant interpretation by closed lambda terms. This is a
simulation into beta reduction, not first-order erasure. Interpretations are
not recursively expanded, so acceptance must establish a strict simulation
for every input rule.\<close>

fun ho_closed_at where
  "ho_closed_at d (HBound n) = (n<d)"
| "ho_closed_at d (HFree n) = False"
| "ho_closed_at d (HConst n) = True"
| "ho_closed_at d (HApp f x) = (ho_closed_at d f \<and> ho_closed_at d x)"
| "ho_closed_at d (HAbs A t) = ho_closed_at (Suc d) t"

lemma ho_closed_lift:
  "ho_closed_at k t \<Longrightarrow> ho_lift d k t=t"
  by (induction t arbitrary: k) auto

lemma ho_closed_beta_subst:
  "ho_closed_at k t \<Longrightarrow> ho_beta_subst u k t=t"
  by (induction t arbitrary: k) auto

lemma ho_closed_free_subst:
  "ho_closed_at k t \<Longrightarrow> ho_subst s d t=t"
  by (induction t arbitrary: k d) auto

lemma ho_closed_context:
  "ho_closed_at (length B) t \<Longrightarrow>
   ho_typeof S V (B@C) t = ho_typeof S [] B t"
proof (induction t arbitrary: B)
  case (HAbs A t)
  have "ho_typeof S V ((A#B)@C) t = ho_typeof S [] (A#B) t"
    by (rule HAbs.IH) (use HAbs.prems in simp)
  then show ?case by simp
qed (auto simp: nth_append split: option.splits ho_type.splits)

fun ho_expand where
  "ho_expand I (HBound n) = HBound n"
| "ho_expand I (HFree n) = HFree n"
| "ho_expand I (HConst n) = I n"
| "ho_expand I (HApp f x) = HApp (ho_expand I f) (ho_expand I x)"
| "ho_expand I (HAbs A t) = HAbs A (ho_expand I t)"

lemma ho_closed_at_mono:
  "ho_closed_at k t \<Longrightarrow> k\<le>j \<Longrightarrow> ho_closed_at j t"
  by (induction t arbitrary: k j) auto

lemma ho_expand_lift:
  "(\<And>n. ho_closed_at 0 (I n)) \<Longrightarrow>
   ho_expand I (ho_lift d k t) = ho_lift d k (ho_expand I t)"
  by (induction t arbitrary: k)
     (auto intro: ho_closed_lift[symmetric] ho_closed_at_mono)

lemma ho_expand_beta_subst:
  assumes closed: "\<And>n. ho_closed_at 0 (I n)"
  shows "ho_expand I (ho_beta_subst u k t) =
         ho_beta_subst (ho_expand I u) k (ho_expand I t)"
  by (induction t arbitrary: k)
     (auto simp: ho_expand_lift[OF closed]
       intro: ho_closed_beta_subst[symmetric] ho_closed_at_mono[OF closed])

lemma ho_expand_free_subst:
  assumes closed: "\<And>n. ho_closed_at 0 (I n)"
  shows "ho_expand I (ho_subst s d t) =
         ho_subst (\<lambda>n. ho_expand I (s n)) d (ho_expand I t)"
  by (induction t arbitrary: d)
     (auto simp: ho_expand_lift[OF closed]
       intro: ho_closed_free_subst[symmetric, OF closed])

lemma ho_expand_type:
  assumes closed: "\<And>n. ho_closed_at 0 (I n)"
    and types: "\<And>n. n<length S \<Longrightarrow> ho_typeof S [] [] (I n) = Some (S!n)"
    and t: "ho_typeof S V B t = Some A"
  shows "ho_typeof S V B (ho_expand I t) = Some A"
  using t
proof (induction t arbitrary: B A)
  case (HConst n)
  have ctx: "ho_typeof S V B (I n) = ho_typeof S [] [] (I n)"
    using ho_closed_context[where B="[]" and C=B and S=S and V=V and t="I n"] closed[of n] by simp
  show ?case using HConst types ctx by (auto split: if_splits)
qed (auto split: option.splits ho_type.splits if_splits)

lemma ho_expand_beta_step:
  assumes closed: "\<And>n. ho_closed_at 0 (I n)"
    and step: "ho_step S V [] B t u"
  shows "ho_step S V [] B (ho_expand I t) (ho_expand I u)"
  using step
  by (induction rule: ho_step.induct)
     (auto simp: ho_expand_beta_subst[OF closed] intro: ho_step.intros)

lemma ho_accp_transitive:
  assumes "Wellfounded.accp P x"
  shows "Wellfounded.accp (P\<^sup>+\<^sup>+) x"
  using assms
proof (rule accp_induct)
  fix x
  assume acc0: "Wellfounded.accp P x"
    and ih: "\<forall>y. P y x \<longrightarrow> Wellfounded.accp (P\<^sup>+\<^sup>+) y"
  show "Wellfounded.accp (P\<^sup>+\<^sup>+) x"
  proof (rule accpI)
    fix y assume path: "P\<^sup>+\<^sup>+ y x"
    obtain z where z: "P z x" "P\<^sup>*\<^sup>* y z"
      using path by (induction rule: tranclp_induct) (auto intro: tranclp_into_rtranclp)
    have acc: "Wellfounded.accp (P\<^sup>+\<^sup>+) z" using ih z(1) by blast
    have "(P\<^sup>+\<^sup>+)\<^sup>*\<^sup>* y z"
      using z(2) by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl tranclp.r_into_trancl)
    then show "Wellfounded.accp (P\<^sup>+\<^sup>+) y" by (rule accp_downwards[OF acc])
  qed
qed

theorem ho_beta_simulation_termination:
  assumes closed: "\<And>n. ho_closed_at 0 (I n)"
    and types: "\<And>n. n<length S \<Longrightarrow> ho_typeof S [] [] (I n) = Some (S!n)"
    and simulation: "\<And>t u. ho_step S V R [] t u \<Longrightarrow>
      beta\<^sup>+\<^sup>+ (ho_db 0 (ho_expand I t)) (ho_db 0 (ho_expand I u))"
  shows "wf ((ho_relation S V R A)\<inverse>)"
proof -
  let ?P = "\<lambda>u t. (t,u) \<in> ho_relation S V R A"
  have all: "\<forall>t. Wellfounded.accp ?P t"
  proof
    fix t
    show "Wellfounded.accp ?P t"
    proof (cases "ho_typeof S V [] t = Some A")
      case True
      have typed: "ho_typeof S V [] (ho_expand I t) = Some A"
        by (rule ho_expand_type[OF closed types True])
      have acc: "termip beta (ho_db 0 (ho_expand I t))"
        using ho_empty_rules_beta_termination[OF typed] by simp
      have acc': "termip (beta\<^sup>+\<^sup>+) (ho_db 0 (ho_expand I t))"
        using ho_accp_transitive[OF acc] by (simp add: tranclp_converse)
      show ?thesis
        by (rule ho_accp_simulation[where f="\<lambda>t. ho_db 0 (ho_expand I t)", OF _ acc'])
           (auto simp: ho_relation_def intro: simulation)
    next
      case False
      show ?thesis by (rule accpI) (use False in \<open>auto simp: ho_relation_def\<close>)
    qed
  qed
  have "wfp ?P" by (rule accp_wfpI[OF all])
  then show ?thesis by (simp add: wfp_def converse_unfold)
qed

end
