theory LP_Prolog_Observed_Equation_Rewrite
  imports LP_Prolog_Stable_Observed_Calls LP_Equation_Congruence
begin

text \<open>Rewrite observations only from an equation established in that same
observed call. Endpoints and successful-helper obligations are unchanged.
This supplies no integer typing or arithmetic bound.\<close>

fun lpp_rewrite_success_guard where
  "lpp_rewrite_success_guard s t (LPPSInteger a) = LPPSInteger (lp_equation_replace s t a)"
| "lpp_rewrite_success_guard s t (LPPSEvaluates e a) =
    LPPSEvaluates (lp_equation_replace s t e) (lp_equation_replace s t a)"
| "lpp_rewrite_success_guard s t (LPPSOpaque a) = LPPSOpaque (lp_equation_replace s t a)"

fun lpp_rewrite_observation where
  "lpp_rewrite_observation s t (LPPOGround a) = LPPOGround (lp_equation_replace s t a)"
| "lpp_rewrite_observation s t (LPPOEquation a b) =
    LPPOEquation (lp_equation_replace s t a) (lp_equation_replace s t b)"
| "lpp_rewrite_observation s t (LPPOShape G shape a) = LPPOShape G shape (lp_equation_replace s t a)"
| "lpp_rewrite_observation s t (LPPOInteger a) = LPPOInteger (lp_equation_replace s t a)"
| "lpp_rewrite_observation s t (LPPOEvaluation e a) =
    LPPOEvaluation (lp_equation_replace s t e) (lp_equation_replace s t a)"
| "lpp_rewrite_observation s t (LPPOComparison c a b) =
    LPPOComparison c (lp_equation_replace s t a) (lp_equation_replace s t b)"

lemma lpp_rewrite_success_guard_holds:
  assumes "lp_ieval s eta=lp_ieval t eta"
  shows "lpp_success_guard_holds E eta (lpp_rewrite_success_guard s t g) =
    lpp_success_guard_holds E eta g"
  by (cases g) (simp_all add: lp_equation_replace_eval[OF assms])

lemma lpp_rewrite_observation_holds:
  assumes "lp_ieval s eta=lp_ieval t eta"
  shows "lpp_stable_observation_holds operation eta (lpp_rewrite_observation s t observation) =
    lpp_stable_observation_holds operation eta observation"
  by (cases observation) (simp_all add: lp_equation_replace_eval[OF assms])

lemma lpp_rewrite_observed_call:
  assumes equation: "LPPOEquation s t\<in>set observations"
  shows "lpp_stable_observed_calls operation {((h,ps,b,gs),observations)} P \<subseteq>
    lpp_stable_observed_calls operation
      {((h,ps,b,map (lpp_rewrite_success_guard s t) gs),map (lpp_rewrite_observation s t) observations)} P"
proof
  fix edge
  assume member: "edge\<in>lpp_stable_observed_calls operation {((h,ps,b,gs),observations)} P"
  obtain a sigma eta where edge: "edge=(a,lpp_success_atom_eval b eta)"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and observed: "list_all (lpp_stable_observation_holds operation eta) observations"
    and helpers: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    using member by (auto simp: lpp_stable_observed_calls_def)
  have equal: "lp_ieval s eta=lp_ieval t eta"
    using observed equation by (auto simp: list_all_iff)
  have guards': "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta)
      (map (lpp_rewrite_success_guard s t) gs)"
    using guards by (simp add: list_all_iff lpp_rewrite_success_guard_holds[OF equal])
  have observed': "list_all (lpp_stable_observation_holds operation eta)
      (map (lpp_rewrite_observation s t) observations)"
    using observed by (simp add: list_all_iff lpp_rewrite_observation_holds[OF equal])
  show "edge\<in>lpp_stable_observed_calls operation
      {((h,ps,b,map (lpp_rewrite_success_guard s t) gs),map (lpp_rewrite_observation s t) observations)} P"
    unfolding edge lpp_stable_observed_calls_def
    using matching guards' observed' helpers by blast
qed

text \<open>Enrichment retains original typing and shape observations. It is
therefore suitable before residual projection, which may need both a symbolic
endpoint type and the normalized arithmetic expression.\<close>

lemma lpp_enrich_observed_call:
  assumes equation: "LPPOEquation s t\<in>set observations"
  shows "lpp_stable_observed_calls operation {((h,ps,b,gs),observations)} P \<subseteq>
    lpp_stable_observed_calls operation
      {((h,ps,b,gs @ map (lpp_rewrite_success_guard s t) gs),observations @ map (lpp_rewrite_observation s t) observations)} P"
proof
  fix edge
  assume member: "edge\<in>lpp_stable_observed_calls operation {((h,ps,b,gs),observations)} P"
  obtain a sigma eta where edge: "edge=(a,lpp_success_atom_eval b eta)"
    and matching: "lpp_success_iatom_subst a sigma=lpp_success_atom_eval h eta"
    and guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and observed: "list_all (lpp_stable_observation_holds operation eta) observations"
    and helpers: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    using member by (auto simp: lpp_stable_observed_calls_def)
  have equal: "lp_ieval s eta=lp_ieval t eta"
    using observed equation by (auto simp: list_all_iff)
  have guards': "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta)
      (map (lpp_rewrite_success_guard s t) gs)"
    using guards by (simp add: list_all_iff lpp_rewrite_success_guard_holds[OF equal])
  have observed': "list_all (lpp_stable_observation_holds operation eta)
      (map (lpp_rewrite_observation s t) observations)"
    using observed by (simp add: list_all_iff lpp_rewrite_observation_holds[OF equal])
  have combined_guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta)
      (gs @ map (lpp_rewrite_success_guard s t) gs)"
    using guards guards' by simp
  have combined_observed: "list_all (lpp_stable_observation_holds operation eta)
      (observations @ map (lpp_rewrite_observation s t) observations)"
    using observed observed' by simp
  show "edge\<in>lpp_stable_observed_calls operation
      {((h,ps,b,gs @ map (lpp_rewrite_success_guard s t) gs),observations @ map (lpp_rewrite_observation s t) observations)} P"
    unfolding edge lpp_stable_observed_calls_def
    using matching combined_guards combined_observed helpers by blast
qed

ML \<open>
val checked = [@{thm lpp_rewrite_observed_call}, @{thm lpp_enrich_observed_call}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted observed equation rewrite dependency" else ();
\<close>
end
