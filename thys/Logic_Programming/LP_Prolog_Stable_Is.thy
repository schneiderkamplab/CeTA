theory LP_Prolog_Stable_Is
  imports LP_Prolog_Stable_Comparison LP_Prolog_Finite_Normalization
begin

definition lpp_stable_is_outcome where
  "lpp_stable_is_outcome operation a e outcome =
    (lpp_finite_is_outcome a e outcome \<and>
      (outcome=LPPBuiltinError \<or> (\<exists>f.
        lpp_stable_scalar_evaluation operation e (LPIFun (LPCUser f) []) \<and>
        outcome=(case lpp_scalar_unifier a f of None \<Rightarrow> LPPBuiltinFailure
          | Some mu \<Rightarrow> LPPBuiltinSuccess mu))))"

lemma lpp_stable_is_refines_finite:
  "lpp_stable_is_outcome operation a e outcome \<Longrightarrow> lpp_finite_is_outcome a e outcome"
  by (simp add: lpp_stable_is_outcome_def)

lemma lpp_stable_is_preserves_errors:
  "lpp_stable_is_outcome operation a e LPPBuiltinError = lpp_finite_is_outcome a e LPPBuiltinError"
  by (simp add: lpp_stable_is_outcome_def)

lemma lpp_stable_is_success_evidence:
  assumes success: "lpp_stable_is_outcome operation a e (LPPBuiltinSuccess mu)"
  shows "lpp_stable_scalar_evaluation operation e (lp_isubst a mu) \<and> lp_isubst e mu=e"
proof -
  obtain f where evaluated: "lpp_stable_scalar_evaluation operation e (LPIFun (LPCUser f) [])"
    and chosen: "lpp_scalar_unifier a f=Some mu"
    using success by (auto simp: lpp_stable_is_outcome_def split: option.splits)
  have ground: "lp_seg_ground e" using lpp_stable_scalar_evaluation_ground[OF evaluated] by blast
  show ?thesis using evaluated lpp_scalar_unifier_sound[OF chosen]
    by (simp add: lp_seg_ground_subst[OF ground])
qed

lemma lpp_stable_is_integer_exact:
  assumes compatible: "lpp_stable_integer_operations operation"
    and evaluated: "lpp_integer_evaluation e n"
  shows "lpp_stable_is_outcome operation a e outcome = lpp_integer_is_outcome a e outcome"
  using lpp_stable_evaluation_integer_exact[OF compatible evaluated]
  by (auto simp: lpp_stable_is_outcome_def lpp_finite_is_integer[OF evaluated]
    lpp_integer_is_outcome_exact[OF evaluated] lpp_integer_value_def lpp_scalar_integer_unifier
    split: option.splits)

ML \<open>
val checked = [@{thm lpp_stable_is_refines_finite}, @{thm lpp_stable_is_preserves_errors},
  @{thm lpp_stable_is_success_evidence}, @{thm lpp_stable_is_integer_exact}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable is dependency" else ();
\<close>
end
