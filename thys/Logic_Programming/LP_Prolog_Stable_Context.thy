theory LP_Prolog_Stable_Context
  imports LP_Prolog_Stable_Source LP_Prolog_Evaluation_Context
begin

text \<open>The existing observation datatype retains its source expressions
and bindings. Comparison observations are strengthened, while all existing
facts remain required. This does not initialize or transfer a saved alternative.\<close>

fun lpp_stable_observation_holds where
  "lpp_stable_observation_holds operation eta (LPPOComparison c a b) =
    lpp_stable_compare_outcome operation c (lp_ieval a eta) (lp_ieval b eta)
      (LPPBuiltinSuccess LPIVar)"
| "lpp_stable_observation_holds operation eta observation =
    lpp_evaluation_observation_holds (lpp_stable_scalar_evaluation operation) eta observation"

lemma lpp_stable_observation_refines:
  "lpp_stable_observation_holds operation eta observation \<Longrightarrow>
    lpp_evaluation_observation_holds (lpp_stable_scalar_evaluation operation) eta observation"
  by (cases observation) (auto dest: lpp_stable_compare_refines_finite)

lemma lpp_stable_observation_substitute:
  "lpp_stable_observation_holds operation eta (lpp_numeric_observation_substitute observation mu) =
    lpp_stable_observation_holds operation (\<lambda>x. lp_ieval (mu x) eta) observation"
  by (cases observation) (simp_all add: lp_ieval_finite_subst)

lemma lpp_stable_comparison_success_subst:
  assumes observed: "lpp_stable_compare_outcome operation c a b (LPPBuiltinSuccess LPIVar)"
  shows "lpp_stable_compare_outcome operation c (lp_isubst a sigma) (lp_isubst b sigma)
    (LPPBuiltinSuccess LPIVar)"
  using observed lpp_stable_compare_values_subst[of operation c a b _ sigma]
    lpp_finite_comparison_subst[of c a b "LPPBuiltinSuccess LPIVar" sigma]
  by (auto simp: lpp_stable_compare_outcome_def split: if_splits)

lemma lpp_stable_observation_subst:
  assumes observed: "lpp_stable_observation_holds operation eta observation"
  shows "lpp_stable_observation_holds operation (\<lambda>x. lp_isubst (eta x) sigma) observation"
  using observed by (cases observation)
    (auto simp: lp_ieval_subst[symmetric] lp_seg_ground_subst
      intro: lpp_stable_scalar_evaluation_subst lpp_is_integer_subst
        lp_return_shape_subst lpp_stable_comparison_success_subst)

ML \<open>
val checked = [@{thm lpp_stable_observation_refines}, @{thm lpp_stable_observation_substitute},
  @{thm lpp_stable_comparison_success_subst}, @{thm lpp_stable_observation_subst}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable context dependency" else ();
\<close>
end
