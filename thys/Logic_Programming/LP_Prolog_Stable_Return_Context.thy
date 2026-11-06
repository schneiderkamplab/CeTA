theory LP_Prolog_Stable_Return_Context
 imports LP_Prolog_Stable_Context LP_Prolog_Evaluation_Refresh LP_Prolog_Actual_Returns
begin

definition lpp_stable_context_holds where
  "lpp_stable_context_holds operation P ctx eta =
    (lpp_evaluation_context_holds (lpp_stable_scalar_evaluation operation) P ctx eta \<and>
      (case ctx of (facts,guards,observations) \<Rightarrow>
        list_all (lpp_stable_observation_holds operation eta) observations))"

lemma lpp_stable_context_runtime_subst:
  assumes known: "lpp_stable_context_holds operation P ctx eta"
  shows "lpp_stable_context_holds operation P ctx (\<lambda>x. lp_isubst (eta x) sigma)"
  using known lpp_evaluation_context_runtime_subst[where E="lpp_stable_scalar_evaluation operation",
    OF lpp_stable_scalar_evaluation_subst]
  by (cases ctx) (auto simp: lpp_stable_context_holds_def list_all_iff
    intro: lpp_stable_observation_subst)

lemma lpp_stable_context_substitute:
  "lpp_stable_context_holds operation P (lpp_source_context_subst ctx mu) eta =
    lpp_stable_context_holds operation P ctx (\<lambda>x. lp_ieval (mu x) eta)"
  by (cases ctx) (simp add: lpp_stable_context_holds_def lpp_evaluation_context_substitute
    lpp_stable_observation_substitute list_all_iff lpp_evaluation_context_holds_def
    lpp_success_atom_subst_eval lpp_success_guard_subst_eval lpp_evaluation_observation_substitute)

lemma lpp_stable_context_join:
  "lpp_stable_context_holds operation P (lpp_join_source_context left right) eta =
    (lpp_stable_context_holds operation P left eta \<and>
     lpp_stable_context_holds operation P right eta)"
  by (cases left; cases right)
    (auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def)

text \<open>Every incoming saved frame must establish the context. A successful
helper answer preserves it through the existing answer relation, independently
of helper termination. No facts from a different successful path initialize a
resumed failure alternative.\<close>

lemma lpp_stable_actual_return_preserves_context:
  assumes actual: "lp_actual_answer (lpp_domain_answers P B U D) ss eta"
    and initialized: "list_all (\<lambda>frame. lpp_stable_context_holds operation SP ctx (snd frame)) ss"
  shows "lpp_stable_context_holds operation SP ctx eta"
  by (rule lpp_actual_return_substitution_property[OF
    lpp_stable_context_runtime_subst actual initialized])

lemma lpp_stable_return_preserves_bound:
  assumes actual: "lp_actual_answer (lpp_domain_answers P B U D) ss eta"
    and initialized: "list_all (\<lambda>frame.
      lpp_stable_scalar_evaluation operation (lp_ieval expression (snd frame)) v) ss"
    and evaluated: "lpp_stable_scalar_evaluation operation (lp_ieval expression eta) w"
  shows "lpp_scalar_floor v=lpp_scalar_floor w"
proof -
  have stable: "lpp_stable_scalar_evaluation operation (lp_ieval expression (\<lambda>x. lp_isubst (rho x) sigma)) v"
    if known: "lpp_stable_scalar_evaluation operation (lp_ieval expression rho) v" for rho sigma
    using lpp_stable_scalar_evaluation_subst[OF known, of sigma]
      lpp_stable_scalar_evaluation_ground[OF known]
    by (simp add: lp_ieval_subst lp_seg_ground_subst)
  have prior: "lpp_stable_scalar_evaluation operation (lp_ieval expression eta) v"
    by (rule lpp_actual_return_substitution_property[OF stable actual initialized])
  have "v=w" by (rule lpp_stable_scalar_evaluation_unique[OF prior evaluated])
  then show ?thesis by simp
qed

ML \<open>
val checked = [@{thm lpp_stable_context_runtime_subst}, @{thm lpp_stable_context_substitute},
  @{thm lpp_stable_context_join}, @{thm lpp_stable_actual_return_preserves_context},
  @{thm lpp_stable_return_preserves_bound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable return context dependency" else ();
\<close>
end
