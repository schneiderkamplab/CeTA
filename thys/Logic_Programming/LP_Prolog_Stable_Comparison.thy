theory LP_Prolog_Stable_Comparison
  imports LP_Prolog_Stable_Integer_Compatibility LP_Prolog_Comparison_Failure
begin

definition lpp_stable_compare_values where
  "lpp_stable_compare_values operation comparison a b truth =
    (\<exists>v w n d m e. lpp_stable_scalar_evaluation operation a v \<and>
      lpp_stable_scalar_evaluation operation b w \<and>
      lpp_scalar_fraction v n d \<and> lpp_scalar_fraction w m e \<and>
      truth=lpp_integer_compare comparison (n*e) (m*d))"

definition lpp_stable_compare_outcome where
  "lpp_stable_compare_outcome operation comparison a b outcome =
    (lpp_finite_compare_outcome comparison a b outcome \<and>
      (outcome=LPPBuiltinError \<or> (\<exists>truth.
        lpp_stable_compare_values operation comparison a b truth \<and>
        outcome=(if truth then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure))))"

lemma lpp_stable_comparison_failure_complement:
  assumes failed: "lpp_stable_compare_outcome operation c a b LPPBuiltinFailure"
  shows "lpp_stable_compare_outcome operation (lpp_comparison_complement c) b a (LPPBuiltinSuccess LPIVar)"
proof -
  have finite: "lpp_finite_compare_outcome (lpp_comparison_complement c) b a (LPPBuiltinSuccess LPIVar)"
    using failed lpp_finite_comparison_failure_complement
    by (auto simp: lpp_stable_compare_outcome_def)
  have truth: "lpp_stable_compare_values operation c a b False"
    using failed by (auto simp: lpp_stable_compare_outcome_def split: if_splits)
  have complement: "lpp_stable_compare_values operation (lpp_comparison_complement c) b a True"
    using truth unfolding lpp_stable_compare_values_def
    by (metis lpp_comparison_complement_truth)
  show ?thesis using finite complement by (auto simp: lpp_stable_compare_outcome_def)
qed

lemma lpp_stable_compare_values_exact:
  assumes left: "lpp_stable_scalar_evaluation operation a v"
    and right: "lpp_stable_scalar_evaluation operation b w"
    and lv: "lpp_scalar_fraction v n d" and rv: "lpp_scalar_fraction w m e"
  shows "lpp_stable_compare_values operation comparison a b truth \<longleftrightarrow>
    truth=lpp_integer_compare comparison (n*e) (m*d)"
proof
  assume observed: "lpp_stable_compare_values operation comparison a b truth"
  obtain v2 w2 n2 d2 m2 e2 where evl: "lpp_stable_scalar_evaluation operation a v2"
    and evr: "lpp_stable_scalar_evaluation operation b w2"
    and fl: "lpp_scalar_fraction v2 n2 d2" and fr: "lpp_scalar_fraction w2 m2 e2"
    and compared: "truth=lpp_integer_compare comparison (n2*e2) (m2*d2)"
    using observed unfolding lpp_stable_compare_values_def by blast
  have veq: "v=v2" by (rule lpp_stable_scalar_evaluation_unique[OF left evl])
  have weq: "w=w2" by (rule lpp_stable_scalar_evaluation_unique[OF right evr])
  have nf: "(n,d)=(n2,d2)" by (rule lpp_scalar_fraction_unique[OF lv]) (use fl veq in simp)
  have mf: "(m,e)=(m2,e2)" by (rule lpp_scalar_fraction_unique[OF rv]) (use fr weq in simp)
  show "truth=lpp_integer_compare comparison (n*e) (m*d)" using nf mf compared by simp
next
  assume compared: "truth=lpp_integer_compare comparison (n*e) (m*d)"
  show "lpp_stable_compare_values operation comparison a b truth"
    unfolding lpp_stable_compare_values_def
    by (rule exI[of _ v], rule exI[of _ w], rule exI[of _ n], rule exI[of _ d],
        rule exI[of _ m], rule exI[of _ e]) (use left right lv rv compared in simp)
qed

lemma lpp_stable_compare_refines_finite:
  "lpp_stable_compare_outcome operation comparison a b outcome \<Longrightarrow>
    lpp_finite_compare_outcome comparison a b outcome"
  by (simp add: lpp_stable_compare_outcome_def)

lemma lpp_stable_compare_preserves_errors:
  "lpp_stable_compare_outcome operation comparison a b LPPBuiltinError =
    lpp_finite_compare_outcome comparison a b LPPBuiltinError"
  by (simp add: lpp_stable_compare_outcome_def)

lemma lpp_stable_compare_integer_exact:
  assumes compatible: "lpp_stable_integer_operations operation"
    and left: "lpp_integer_evaluation a n" and right: "lpp_integer_evaluation b m"
  shows "lpp_stable_compare_outcome operation comparison a b outcome =
    lpp_integer_compare_outcome comparison a b outcome"
  using lpp_stable_compare_values_exact[OF lpp_integer_evaluation_stable[OF compatible left]
    lpp_integer_evaluation_stable[OF compatible right]
    lpp_integer_scalar_observation lpp_integer_scalar_observation, where comparison=comparison]
  by (auto simp: lpp_stable_compare_outcome_def lpp_finite_comparison_integer[OF left right]
    lpp_integer_compare_outcome_exact[OF left right] split: if_splits)

lemma lpp_stable_compare_integer_bound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and counter: "lpp_integer_evaluation a k"
    and bound: "lpp_stable_scalar_evaluation operation b v"
    and fraction: "lpp_scalar_fraction v n d"
    and success: "lpp_stable_compare_outcome operation LPPIntLessEqual a b (LPPBuiltinSuccess LPIVar)"
  shows "k\<le>lpp_scalar_floor v"
proof -
  have exact: "lpp_stable_compare_values operation LPPIntLessEqual a b truth = (truth=(k*d\<le>n))" for truth
    using lpp_stable_compare_values_exact[OF lpp_integer_evaluation_stable[OF compatible counter]
      bound lpp_integer_scalar_observation fraction, where comparison=LPPIntLessEqual] by simp
  have "k*d\<le>n" using success exact by (auto simp: lpp_stable_compare_outcome_def split: if_splits)
  then show ?thesis
    using lpp_fraction_floor_bound[OF lpp_scalar_fraction_denominator[OF fraction], where k=k]
      lpp_scalar_floor_exact[OF fraction] by simp
qed

lemma lpp_stable_compare_upper_bound:
  assumes compatible: "lpp_stable_integer_operations operation"
    and counter: "lpp_integer_evaluation a k"
    and bound: "lpp_stable_scalar_evaluation operation b v"
    and fraction: "lpp_scalar_fraction v n d"
    and comparison: "comparison=LPPIntLess \<or> comparison=LPPIntLessEqual"
    and success: "lpp_stable_compare_outcome operation comparison a b (LPPBuiltinSuccess LPIVar)"
  shows "k\<le>lpp_scalar_floor v"
proof -
  have exact: "lpp_stable_compare_values operation comparison a b truth =
      (truth=lpp_integer_compare comparison (k*d) n)" for truth
    using lpp_stable_compare_values_exact[OF lpp_integer_evaluation_stable[OF compatible counter]
      bound lpp_integer_scalar_observation fraction, where comparison=comparison] by simp
  have "lpp_integer_compare comparison (k*d) n"
    using success exact by (auto simp: lpp_stable_compare_outcome_def split: if_splits)
  then have "k*d\<le>n" using comparison by auto
  then show ?thesis
    using lpp_fraction_floor_bound[OF lpp_scalar_fraction_denominator[OF fraction], where k=k]
      lpp_scalar_floor_exact[OF fraction] by simp
qed

lemma lpp_stable_compare_values_subst:
  assumes observed: "lpp_stable_compare_values operation comparison a b truth"
  shows "lpp_stable_compare_values operation comparison (lp_isubst a sigma) (lp_isubst b sigma) truth"
proof -
  have "lp_seg_ground a" "lp_seg_ground b"
    using observed lpp_stable_scalar_evaluation_ground
    by (auto simp: lpp_stable_compare_values_def)
  then show ?thesis using observed by (simp add: lp_seg_ground_subst)
qed

lemma lpp_stable_compare_total:
  assumes compatible: "lpp_stable_integer_operations operation"
    and ground: "lp_seg_ground a" "lp_seg_ground b"
  shows "\<exists>outcome. lpp_stable_compare_outcome operation comparison a b outcome"
proof (cases "(\<exists>n. lpp_integer_evaluation a n) \<and> (\<exists>m. lpp_integer_evaluation b m)")
  case True
  then obtain n m where left: "lpp_integer_evaluation a n" and right: "lpp_integer_evaluation b m" by blast
  show ?thesis by (simp only: lpp_stable_compare_integer_exact[OF compatible left right]
    lpp_integer_compare_outcome_exact[OF left right]; blast)
next
  case False
  have "lpp_stable_compare_outcome operation comparison a b LPPBuiltinError"
    using False ground by (auto simp: lpp_stable_compare_preserves_errors lpp_finite_compare_outcome_def)
  then show ?thesis by blast
qed

ML \<open>
val checked = [@{thm lpp_stable_compare_values_exact}, @{thm lpp_stable_compare_refines_finite},
  @{thm lpp_stable_compare_preserves_errors}, @{thm lpp_stable_compare_integer_exact},
  @{thm lpp_stable_compare_integer_bound}, @{thm lpp_stable_compare_upper_bound},
  @{thm lpp_stable_compare_values_subst}, @{thm lpp_stable_compare_total}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable comparison dependency" else ();
\<close>
end
