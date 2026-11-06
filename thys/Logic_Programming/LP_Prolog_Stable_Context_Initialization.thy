theory LP_Prolog_Stable_Context_Initialization
 imports LP_Prolog_Stable_Bound_Projection LP_Prolog_Evaluation_Comparison
begin

lemma lpp_stable_context_add_observation:
  assumes initialized: "lpp_stable_context_holds operation P ctx eta"
    and observation: "lpp_stable_observation_holds operation eta observation"
  shows "lpp_stable_context_holds operation P (lpp_add_numeric_observation observation ctx) eta"
  using initialized observation lpp_stable_observation_refines[OF observation]
  by (cases ctx) (auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def)

lemma lpp_stable_context_comparison_success:
  assumes initialized: "lpp_stable_context_holds operation P ctx eta"
    and success: "lpp_stable_compare_outcome operation c (lp_ieval a eta) (lp_ieval b eta)
      (LPPBuiltinSuccess LPIVar)"
  shows "lpp_stable_context_holds operation P
    (lpp_add_numeric_observation (LPPOComparison c a b) ctx) eta"
  by (rule lpp_stable_context_add_observation[OF initialized]) (use success in simp)

lemma lpp_stable_context_is_success:
  assumes initialized: "lpp_stable_context_holds operation P ctx eta"
    and success: "lpp_stable_is_outcome operation (lp_ieval a eta) (lp_ieval e eta)
      (LPPBuiltinSuccess mu)"
  shows "lpp_stable_context_holds operation P
    (lpp_add_numeric_observation (LPPOEvaluation e a) ctx)
      (\<lambda>x. lp_isubst (eta x) mu)"
proof -
  have old: "lpp_stable_context_holds operation P ctx (\<lambda>x. lp_isubst (eta x) mu)"
    by (rule lpp_stable_context_runtime_subst[OF initialized])
  have evidence: "lpp_stable_observation_holds operation (\<lambda>x. lp_isubst (eta x) mu)
    (LPPOEvaluation e a)"
    using lpp_stable_is_success_evidence[OF success]
    by (simp add: lp_ieval_subst[symmetric])
  show ?thesis by (rule lpp_stable_context_add_observation[OF old evidence])
qed

text \<open>Only the successful continuation gets the new observation. The
failure and error edges must use their original checked contexts.\<close>

ML \<open>
val checked = [@{thm lpp_stable_context_add_observation},
  @{thm lpp_stable_context_comparison_success}, @{thm lpp_stable_context_is_success}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable initialization dependency" else ();
\<close>
end
