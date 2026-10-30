theory LP_Prolog_Finite_Comparison
  imports LP_Prolog_Builtin_Domain
begin

text \<open>Finite ground comparison operands admit a terminating source envelope
without treating their values as integers. Integer evaluations retain their
exact comparison. Other finite operands conservatively permit identity success,
failure and uncaught error. In particular this makes no replacement of binary64
arithmetic by integer arithmetic. Cyclic operands are outside this domain.\<close>

lemma lpp_integer_evaluation_ground:
  "lpp_integer_evaluation t n \<Longrightarrow> lp_seg_ground t"
  by (induct rule: lpp_integer_evaluation.induct)
    (auto simp: lpp_integer_value_def intro: lp_seg_ground.intros)

definition lpp_finite_compare_outcome where
  "lpp_finite_compare_outcome comparison a b outcome =
    (lp_seg_ground a \<and> lp_seg_ground b \<and>
      (if (\<exists>n. lpp_integer_evaluation a n) \<and> (\<exists>m. lpp_integer_evaluation b m)
       then lpp_integer_compare_outcome comparison a b outcome
       else outcome=LPPBuiltinSuccess LPIVar \<or> outcome=LPPBuiltinFailure \<or> outcome=LPPBuiltinError))"

lemma lpp_finite_comparison_integer:
  assumes left: "lpp_integer_evaluation a n" and right: "lpp_integer_evaluation b m"
  shows "lpp_finite_compare_outcome comparison a b outcome = lpp_integer_compare_outcome comparison a b outcome"
  using left right lpp_integer_evaluation_ground[OF left] lpp_integer_evaluation_ground[OF right]
  by (auto simp: lpp_finite_compare_outcome_def)

lemma lpp_finite_comparison_total:
  assumes "lp_seg_ground a" "lp_seg_ground b"
  shows "\<exists>outcome. lpp_finite_compare_outcome comparison a b outcome"
proof (cases "(\<exists>n. lpp_integer_evaluation a n) \<and> (\<exists>m. lpp_integer_evaluation b m)")
  case True
  then obtain n m where left: "lpp_integer_evaluation a n" and right: "lpp_integer_evaluation b m" by blast
  show ?thesis by (simp only: lpp_finite_comparison_integer[OF left right]
    lpp_integer_compare_outcome_exact[OF left right]; blast)
next
  case False
  show ?thesis using assms False by (auto simp: lpp_finite_compare_outcome_def)
qed

lemma lpp_finite_comparison_subst:
  assumes "lpp_finite_compare_outcome comparison a b outcome"
  shows "lpp_finite_compare_outcome comparison (lp_isubst a sigma) (lp_isubst b sigma) outcome"
  using assms by (auto simp: lpp_finite_compare_outcome_def lp_seg_ground_subst)

lemma lpp_integer_comparison_finite:
  assumes "lpp_integer_compare_outcome comparison a b outcome"
  shows "lpp_finite_compare_outcome comparison a b outcome"
proof -
  obtain n m where left: "lpp_integer_evaluation a n" and right: "lpp_integer_evaluation b m"
    using assms by (auto simp: lpp_integer_compare_outcome_def)
  show ?thesis using assms by (simp only: lpp_finite_comparison_integer[OF left right])
qed

end
