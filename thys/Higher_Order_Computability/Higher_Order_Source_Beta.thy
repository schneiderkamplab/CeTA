theory Higher_Order_Source_Beta
  imports Higher_Order_Source_Substitution
begin

context ho_source_neutral_reducibility
begin

lemma source_abstraction_reduct:
  "ho_step S V R B (HAbs A t) u \<Longrightarrow>
    \<exists>v. u=HAbs A v \<and> ho_step S V R (A#B) t v"
  by (erule ho_step.cases) (auto dest: rule_instance_constant_head)

lemma source_beta_reduct:
  "ho_step S V R B (HApp (HAbs A t) x) u \<Longrightarrow>
    u=ho_beta_subst x 0 t \<or>
    (\<exists>v. ho_step S V R (A#B) t v \<and> u=HApp (HAbs A v) x) \<or>
    (\<exists>y. ho_step S V R B x y \<and> u=HApp (HAbs A t) y)"
  by (erule ho_step.cases)
    (auto dest: rule_instance_constant_head source_abstraction_reduct)

theorem source_computable_beta_expansion:
  assumes body_sn: "Wellfounded.accp (\<lambda>v t. ho_step S V R (A#B) t v) t"
    and arg_sn: "source.strongly_normalizing x"
    and ty: "ho_typeof S V B (HApp (HAbs A t) x)=Some C"
    and contractum: "source.computable C (ho_beta_subst x 0 t)"
  shows "source.computable C (HApp (HAbs A t) x)"
  using body_sn arg_sn ty contractum
proof (induction t arbitrary: x rule: accp.induct)
  case (accI t)
  note body_ih = accI.IH
  show ?case using accI.prems
  proof (induction x rule: accp.induct)
    case (accI x)
    have xt: "ho_typeof S V B x=Some A"
      using accI.prems(1) by (auto split: option.splits ho_type.splits if_splits)
    have reducts: "source.computable C u" if st: "ho_step S V R B (HApp (HAbs A t) x) u" for u
    proof -
      from source_beta_reduct[OF st] show ?thesis
      proof (elim disjE exE conjE)
        assume "u=ho_beta_subst x 0 t"
        then show ?thesis using accI.prems(2) by simp
      next
        fix v assume tv: "ho_step S V R (A#B) t v" and eq: "u=HApp (HAbs A v) x"
        have sub: "ho_step S V R B (ho_beta_subst x 0 t) (ho_beta_subst x 0 v)"
          using ho_source_step_beta_substitution[OF tv zero, where D="[]" and T=A and C=B and x=x] xt by simp
        have comp: "source.computable C (ho_beta_subst x 0 v)"
          by (rule source.computable_reduction[OF accI.prems(2) sub])
        have vt: "ho_typeof S V B (HApp (HAbs A v) x)=Some C"
          by (rule ho_zero_arity_step_type[OF ho_step.app_left[OF ho_step.abs[OF tv]] zero accI.prems(1)])
        have snx: "source.strongly_normalizing x" by (rule accp.accI[OF accI.hyps])
        show ?thesis using body_ih[OF tv snx vt comp] unfolding eq .
      next
        fix y assume xy: "ho_step S V R B x y" and eq: "u=HApp (HAbs A t) y"
        have sub: "(ho_step S V R B)\<^sup>*\<^sup>* (ho_beta_subst x 0 t) (ho_beta_subst y 0 t)"
          using ho_source_beta_argument_steps[OF xy zero, where B="[]" and t=t] by simp
        have comp: "source.computable C (ho_beta_subst y 0 t)"
          by (rule source.computable_reductions[OF sub accI.prems(2)])
        have yt: "ho_typeof S V B (HApp (HAbs A t) y)=Some C"
          by (rule ho_zero_arity_step_type[OF ho_step.app_right[OF xy] zero accI.prems(1)])
        show ?thesis using accI.IH[OF xy yt comp] unfolding eq .
      qed
    qed
    show ?case by (rule source_neutral.neutral_computable[OF accI.prems(1)])
      (auto simp: ho_source_neutral_def intro: reducts)
  qed
qed

lemma source_abstraction_SN:
  "Wellfounded.accp (\<lambda>v t. ho_step S V R (A#B) t v) t \<Longrightarrow>
    source.strongly_normalizing (HAbs A t)"
proof (induction t rule: accp.induct)
  case (accI t)
  show ?case
  proof (rule accp.accI)
    fix u assume "ho_step S V R B (HAbs A t) u"
    then obtain v where "u=HAbs A v" and "ho_step S V R (A#B) t v"
      using source_abstraction_reduct by blast
    then show "source.strongly_normalizing u" using accI.IH by blast
  qed
qed

theorem source_computable_abstraction:
  assumes ty: "ho_typeof S V B (HAbs A t)=Some (HArrow A C)"
    and body_sn: "Wellfounded.accp (\<lambda>v t. ho_step S V R (A#B) t v) t"
    and instances: "\<And>x. source.computable A x \<Longrightarrow>
      source.computable C (ho_beta_subst x 0 t)"
  shows "source.computable (HArrow A C) (HAbs A t)"
proof -
  have applied: "source.computable C (HApp (HAbs A t) x)"
    if cx: "source.computable A x" for x
  proof -
    have xt: "ho_typeof S V B x=Some A" by (rule source.computable_typed[OF cx])
    have at: "ho_typeof S V B (HApp (HAbs A t) x)=Some C" using ty xt by simp
    show ?thesis by (rule source_computable_beta_expansion[OF body_sn
      source.computable_SN[OF cx] at instances[OF cx]])
  qed
  show ?thesis using ty source_abstraction_SN[OF body_sn] applied by simp
qed

end

end
