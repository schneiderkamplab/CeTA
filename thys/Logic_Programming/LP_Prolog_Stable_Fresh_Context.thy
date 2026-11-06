theory LP_Prolog_Stable_Fresh_Context
 imports LP_Prolog_Stable_Normalization
begin

lemma lpp_stable_context_environment_cong:
  assumes same: "\<And>t. t\<in>set (lpp_context_terms ctx) \<Longrightarrow> lp_ieval t eta=lp_ieval t nu"
  shows "lpp_stable_context_holds operation P ctx eta=lpp_stable_context_holds operation P ctx nu"
proof -
  obtain facts guards observations where shape: "ctx=(facts,guards,observations)"
    by (cases ctx) auto
  have base: "lpp_evaluation_context_holds (lpp_stable_scalar_evaluation operation) P ctx eta=
    lpp_evaluation_context_holds (lpp_stable_scalar_evaluation operation) P ctx nu"
    by (rule lpp_evaluation_context_environment_cong[OF same])
  have each: "lpp_stable_observation_holds operation eta observation=lpp_stable_observation_holds operation nu observation"
    if member: "observation\<in>set observations" for observation
  proof -
    have eq: "lp_ieval t eta=lp_ieval t nu" if "t\<in>set (lpp_context_observation_terms observation)" for t
      by (rule same) (use that member in \<open>auto simp: shape\<close>)
    show ?thesis using eq by (cases observation) auto
  qed
  show ?thesis using base each by (auto simp: shape lpp_stable_context_holds_def list_all_iff)
qed

lemma lpp_stable_context_fresh_eval:
  "lpp_context_fresh x ctx \<Longrightarrow>
    lpp_stable_context_holds operation P ctx (eta(x:=v))=lpp_stable_context_holds operation P ctx eta"
  by (rule lpp_stable_context_environment_cong)
    (auto simp: lpp_context_fresh_def intro: lpp_fresh_term_eval)

lemma lpp_stable_add_evaluation_context:
  "lpp_stable_context_holds operation P ctx eta \<Longrightarrow>
    lpp_stable_scalar_evaluation operation (lp_ieval e eta) (lp_ieval t eta) \<Longrightarrow>
    lpp_stable_context_holds operation P (lpp_add_evaluation_observation e t ctx) eta"
  by (cases ctx) (auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def)

ML \<open>
val checked = [@{thm lpp_stable_context_environment_cong}, @{thm lpp_stable_context_fresh_eval},
  @{thm lpp_stable_add_evaluation_context}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable fresh-context dependency" else ();
\<close>
end
