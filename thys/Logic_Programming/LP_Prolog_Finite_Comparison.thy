theory LP_Prolog_Finite_Comparison
  imports LP_Prolog_Finite_Term_Basis
begin

text \<open>Finite ground comparison operands admit a terminating source envelope
without treating their values as integers. Finite nonground operands raise an error only when both operands are finite.
Integer evaluations retain their
exact comparison. Other finite operands conservatively permit identity success,
failure and uncaught error. In particular this makes no replacement of binary64
arithmetic by integer arithmetic. Cyclic operands are outside this domain.\<close>

lemma lpp_integer_evaluation_ground:
  "lpp_integer_evaluation t n \<Longrightarrow> lp_seg_ground t"
  by (induct rule: lpp_integer_evaluation.induct)
    (auto simp: lpp_integer_value_def intro: lp_seg_ground.intros)

definition lpp_finite_compare_error where
  "lpp_finite_compare_error a b =
    (lpp_finite_term a \<and> lpp_finite_term b \<and>
      \<not>(lp_seg_ground a \<and> lp_seg_ground b))"

lemma lpp_finite_compare_error_legacy:
  "(((\<exists>x. a=LPIVar x) \<and> (lp_seg_ground b \<or> (\<exists>y. b=LPIVar y))) \<or>
     ((\<exists>y. b=LPIVar y) \<and> lp_seg_ground a)) \<Longrightarrow>
    lpp_finite_compare_error a b"
  by (auto simp: lpp_finite_compare_error_def lp_seg_ground.simps
    intro: lpp_ground_finite_term)

lemma lpp_finite_compare_error_finite:
  "lpp_finite_compare_error a b \<Longrightarrow> lpp_finite_term a \<and> lpp_finite_term b"
  by (simp add: lpp_finite_compare_error_def)

lemma lpp_finite_compare_error_ground[simp]:
  "lp_seg_ground a \<Longrightarrow> lp_seg_ground b \<Longrightarrow> \<not>lpp_finite_compare_error a b"
  by (auto simp: lpp_finite_compare_error_def elim: lp_seg_ground.cases)

definition lpp_finite_compare_outcome where
  "lpp_finite_compare_outcome comparison a b outcome =
    ((lpp_finite_compare_error a b \<and> outcome=LPPBuiltinError) \<or>
     (lp_seg_ground a \<and> lp_seg_ground b \<and>
      (if (\<exists>n. lpp_integer_evaluation a n) \<and> (\<exists>m. lpp_integer_evaluation b m)
       then lpp_integer_compare_outcome comparison a b outcome
       else outcome=LPPBuiltinSuccess LPIVar \<or> outcome=LPPBuiltinFailure \<or> outcome=LPPBuiltinError)))"

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
  assumes "lpp_finite_compare_outcome comparison a b outcome" "outcome\<noteq>LPPBuiltinError"
  shows "lpp_finite_compare_outcome comparison (lp_isubst a sigma) (lp_isubst b sigma) outcome"
  using assms by (auto simp: lpp_finite_compare_outcome_def lp_seg_ground_subst split: if_splits)

lemma lpp_integer_comparison_finite:
  assumes "lpp_integer_compare_outcome comparison a b outcome"
  shows "lpp_finite_compare_outcome comparison a b outcome"
proof -
  obtain n m where left: "lpp_integer_evaluation a n" and right: "lpp_integer_evaluation b m"
    using assms by (auto simp: lpp_integer_compare_outcome_def)
  show ?thesis using assms by (simp only: lpp_finite_comparison_integer[OF left right])
qed

lemma lpp_finite_comparison_total_finite:
  assumes "lpp_finite_term a" "lpp_finite_term b"
  shows "\<exists>outcome. lpp_finite_compare_outcome comparison a b outcome"
proof (cases "lp_seg_ground a \<and> lp_seg_ground b")
 case True then show ?thesis using lpp_finite_comparison_total by blast
next
 case False then show ?thesis using assms
   by (auto simp: lpp_finite_compare_error_def lpp_finite_compare_outcome_def)
qed

lemma lpp_finite_comparison_nonerror_ground:
 "lpp_finite_compare_outcome comparison a b outcome \<Longrightarrow>
  outcome\<noteq>LPPBuiltinError \<Longrightarrow> lp_seg_ground a \<and> lp_seg_ground b"
 by (auto simp: lpp_finite_compare_outcome_def)

ML \<open>
val checked = [@{thm lpp_finite_compare_error_legacy},
 @{thm lpp_finite_comparison_total_finite}, @{thm lpp_finite_comparison_nonerror_ground}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite comparison extension" else ();
\<close>

end
