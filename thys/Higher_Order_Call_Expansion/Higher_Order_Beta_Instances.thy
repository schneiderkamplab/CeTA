theory Higher_Order_Beta_Instances
  imports Higher_Order_Definition_Expansion
begin

lemma ho_expansion_subst_lift:
  "n\<le>d \<Longrightarrow>
    ho_subst s (d+k) (ho_lift k n t)=ho_lift k n (ho_subst s d t)"
proof (induction t arbitrary: d n)
  case (HFree x)
  show ?case
    using ho_lift_merge_source[OF HFree.prems, where k=0 and d=k and t="s x"]
    by (simp add: add.commute)
next
  case (HAbs A t)
  have "ho_subst s (Suc d+k) (ho_lift k (Suc n) t)=
      ho_lift k (Suc n) (ho_subst s (Suc d) t)"
    by (rule HAbs.IH) (use HAbs.prems in simp)
  then show ?case by simp
qed auto

lemma ho_expansion_subst_beta:
  "ho_subst s (d+k) (ho_beta_subst u k t)=
    ho_beta_subst (ho_subst s d u) k (ho_subst s (Suc (d+k)) t)"
proof (induction t arbitrary: k)
  case (HBound n)
  have lift: "ho_subst s (d+k) (ho_lift k 0 u)=ho_lift k 0 (ho_subst s d u)"
    by (rule ho_expansion_subst_lift) simp
  show ?case by (auto simp: lift)
next
  case (HFree n)
  have drop: "ho_beta_subst (ho_subst s d u) k (ho_lift (Suc (d+k)) 0 (s n))=
      ho_lift (d+k) 0 (s n)"
    using ho_beta_delete_lift_source[where k=k and d="d+k" and c=0
      and u="ho_subst s d u" and t="s n"] by simp
  show ?case by (simp add: drop)
next
  case (HAbs A t)
  show ?case using HAbs.IH[of "Suc k"] by simp
qed auto

lemma ho_expansion_beta_instance:
  assumes step: "ho_step S G [] D t u"
  shows "ho_step S V R (D@B) (ho_subst s (length D) t) (ho_subst s (length D) u)"
  using step
proof (induction rule: ho_step.induct)
  case (beta D A t u)
  have eq: "ho_subst s (length D) (ho_beta_subst u 0 t)=
      ho_beta_subst (ho_subst s (length D) u) 0 (ho_subst s (Suc (length D)) t)"
    using ho_expansion_subst_beta[where d="length D" and k=0 and s=s and u=u and t=t] by simp
  show ?case by (simp add: eq ho_step.beta)
qed (auto intro: ho_step.intros)

lemma ho_expansion_beta_instances:
  "(ho_step S G [] D)\<^sup>*\<^sup>* t u \<Longrightarrow>
    (ho_step S V R (D@B))\<^sup>*\<^sup>*
      (ho_subst s (length D) t) (ho_subst s (length D) u)"
  by (induction rule: rtranclp_induct)
    (auto intro: rtranclp.rtrancl_into_rtrancl ho_expansion_beta_instance)

end
