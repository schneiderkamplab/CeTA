theory Higher_Order_Call_Expansion
  imports "Higher_Order_Guarded.Higher_Order_Guarded_Code"
begin

text \<open>Local beta-expansion obligations for future definition unfolding.
These lemmas do not claim that beta-normalizing rule right-hand sides or
unfolding definitions preserves source termination. In particular a
computable contractum alone must not hide a nonterminating erased argument.
No executable certificate constructor is added here.\<close>

context ho_source_accessible_reducibility
begin

lemma source_candidate_beta_from_contractum:
  assumes ty: "ho_typeof S V B (HApp (HAbs A t) x)=Some C"
    and arg_sn: "source.strongly_normalizing x"
    and contractum: "source_candidate C (ho_beta_subst x 0 t)"
  shows "source_candidate C (HApp (HAbs A t) x)"
proof -
  have xt: "ho_typeof S V B x=Some A"
    using ty by (auto split: option.splits ho_type.splits if_splits)
  have body_sn: "Wellfounded.accp (\<lambda>v t. ho_step S V R (A#B) t v) t"
    by (rule source_body_SN_from_instance[OF xt source.candidate_SN[OF contractum]])
  show ?thesis
    by (rule source_candidate_beta_expansion[OF body_sn arg_sn ty contractum])
qed

lemma source_candidate_beta_retained_argument:
  assumes ty: "ho_typeof S V B (HApp (HAbs A t) x)=Some C"
    and contractum: "source_candidate C (ho_beta_subst x 0 t)"
    and retained: "ho_direct_application_subterm\<^sup>*\<^sup>* x (ho_beta_subst x 0 t)"
  shows "source_candidate C (HApp (HAbs A t) x)"
proof -
  have root: "Wellfounded.accp application_descent (ho_beta_subst x 0 t)"
    by (rule source_SN_application_descent[OF source.candidate_SN[OF contractum]])
  have arg: "Wellfounded.accp application_descent x"
    by (rule application_subterm_accessible[OF root retained])
  show ?thesis
    by (rule source_candidate_beta_from_contractum[OF ty
      application_descent_SN[OF arg] contractum])
qed

text \<open>The identity beta redex is an immediate positive instance,
independent of symbol names, source rules, and the argument's type.\<close>

lemma source_candidate_beta_identity:
  assumes ty: "ho_typeof S V B (HApp (HAbs A (HBound 0)) x)=Some A"
    and arg: "source_candidate A x"
  shows "source_candidate A (HApp (HAbs A (HBound 0)) x)"
  by (rule source_candidate_beta_retained_argument[OF ty]) (use arg in auto)

end

end
