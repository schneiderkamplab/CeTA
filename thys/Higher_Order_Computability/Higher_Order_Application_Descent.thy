theory Higher_Order_Application_Descent
  imports Higher_Order_Saturated_Neutral
begin

fun ho_direct_application_subterm where
  "ho_direct_application_subterm u (HApp f x) = (u=f \<or> u=x)"
| "ho_direct_application_subterm u t = False"

context ho_source_reducibility
begin

definition application_descent where
  "application_descent u t = (ho_step S V R B t u \<or> ho_direct_application_subterm u t)"

lemma application_descent_from_reducts:
  "(\<And>u. ho_step S V R B t u \<Longrightarrow> Wellfounded.accp application_descent u)
    \<Longrightarrow> Wellfounded.accp application_descent t"
proof (induction t)
  case (HBound n)
  show ?case by (rule accp.accI) (use HBound.prems in \<open>auto simp: application_descent_def\<close>)
next
  case (HFree n)
  show ?case by (rule accp.accI) (use HFree.prems in \<open>auto simp: application_descent_def\<close>)
next
  case (HConst n)
  show ?case by (rule accp.accI) (use HConst.prems in \<open>auto simp: application_descent_def\<close>)
next
  case (HAbs A t)
  show ?case by (rule accp.accI) (use HAbs.prems in \<open>auto simp: application_descent_def\<close>)
next
  case (HApp f x)
  have fa: "Wellfounded.accp application_descent f"
  proof (rule HApp.IH(1))
    fix g assume fg: "ho_step S V R B f g"
    have acc: "Wellfounded.accp application_descent (HApp g x)"
      by (rule HApp.prems[OF ho_step.app_left[OF fg]])
    show "Wellfounded.accp application_descent g" by (rule accp_downward[OF acc]) (simp add: application_descent_def)
  qed
  have xa: "Wellfounded.accp application_descent x"
  proof (rule HApp.IH(2))
    fix y assume xy: "ho_step S V R B x y"
    have acc: "Wellfounded.accp application_descent (HApp f y)"
      by (rule HApp.prems[OF ho_step.app_right[OF xy]])
    show "Wellfounded.accp application_descent y" by (rule accp_downward[OF acc]) (simp add: application_descent_def)
  qed
  show ?case
  proof (rule accp.accI)
    fix u assume "application_descent u (HApp f x)"
    then have "ho_step S V R B (HApp f x) u \<or> u=f \<or> u=x"
      by (simp add: application_descent_def)
    then show "Wellfounded.accp application_descent u" using HApp.prems fa xa by blast
  qed
qed

theorem source_SN_application_descent:
  "Wellfounded.accp (\<lambda>u t. ho_step S V R B t u) t \<Longrightarrow>
    Wellfounded.accp application_descent t"
  by (induction t rule: accp.induct) (rule application_descent_from_reducts, assumption)

corollary computable_application_descent:
  "source.computable A t \<Longrightarrow> Wellfounded.accp application_descent t"
  by (rule source_SN_application_descent, rule source.computable_SN)

lemma application_subterm_accessible:
  assumes acc: "Wellfounded.accp application_descent t"
    and path: "ho_direct_application_subterm\<^sup>*\<^sup>* u t"
  shows "Wellfounded.accp application_descent u"
proof -
  have "application_descent\<^sup>*\<^sup>* u t"
    using path by (induction rule: rtranclp_induct)
      (auto simp: application_descent_def intro: rtranclp.rtrancl_into_rtrancl)
  then show ?thesis by (rule accp_downwards[OF acc])
qed

lemma application_descent_SN:
  "Wellfounded.accp application_descent t \<Longrightarrow>
    Wellfounded.accp (\<lambda>u t. ho_step S V R B t u) t"
proof -
  have subset: "(\<lambda>u t. ho_step S V R B t u)\<le>application_descent"
    by (auto simp: application_descent_def)
  assume "Wellfounded.accp application_descent t"
  then show ?thesis using accp_subset[OF subset] by auto
qed

theorem base_application_subterm_computable:
  assumes root: "source.computable A t"
    and path: "ho_direct_application_subterm\<^sup>*\<^sup>* u t"
    and ty: "ho_typeof S V B u=Some (HBase b)"
  shows "source.computable (HBase b) u"
proof -
  have acc: "Wellfounded.accp application_descent u"
    by (rule application_subterm_accessible[OF computable_application_descent[OF root] path])
  show ?thesis using application_descent_SN[OF acc] ty by simp
qed

end

end
