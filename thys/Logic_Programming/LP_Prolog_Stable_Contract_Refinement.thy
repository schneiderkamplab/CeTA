theory LP_Prolog_Stable_Contract_Refinement
 imports LP_Prolog_Stable_Length
begin

lemma lp_answer_contract_transition_refinement:
  assumes refines: "\<And>xs ev ys. U xs ev ys \<Longrightarrow> T xs ev ys"
    and contract: "lp_answer_contract T ss R t ret"
  shows "lp_answer_contract U ss R t ret"
proof -
  have included: "lp_answer_steps U \<subseteq> lp_answer_steps T"
    using refines by (auto simp: lp_answer_steps_def)
  have paths: "(lp_answer_steps U)\<^sup>* \<subseteq> (lp_answer_steps T)\<^sup>*"
    by (rule rtrancl_mono[OF included])
  have sn: "SN_on (lp_answer_steps U) {ss}"
    by (rule SN_on_subset1[OF _ included]) (use contract in \<open>simp add: lp_answer_contract_def\<close>)
  have covered: "lp_answers_covered U ss (\<lambda>rho. (t,ret rho)\<in>R\<^sup>*)"
  proof (unfold lp_answers_covered_def, intro allI impI)
    fix us rho vs
    assume path: "(ss,us)\<in>(lp_answer_steps U)\<^sup>*" and event: "U us (Some rho) vs"
    have old_path: "(ss,us)\<in>(lp_answer_steps T)\<^sup>*" by (rule subsetD[OF paths path])
    have old_event: "T us (Some rho) vs" by (rule refines[OF event])
    show "(t,ret rho)\<in>R\<^sup>*" using contract old_path old_event
      by (auto simp: lp_answer_contract_def lp_answers_covered_def)
  qed
  show ?thesis using sn covered by (simp add: lp_answer_contract_def)
qed

lemma lpp_stable_domain_answers_refine:
  "lpp_domain_answers P B (lpp_stable_source_builtin operation) D ss ev tt \<Longrightarrow>
    lpp_domain_answers P B lpp_finite_source_builtin D ss ev tt"
  by (auto simp: lpp_domain_answers_def intro: lpp_stable_answer_transition_refines)

lemma lpp_stable_contract_from_finite:
  "lp_answer_contract (lpp_domain_answers P B lpp_finite_source_builtin D) ss R t ret \<Longrightarrow>
    lp_answer_contract (lpp_domain_answers P B (lpp_stable_source_builtin operation) D) ss R t ret"
  by (rule lp_answer_contract_transition_refinement[OF lpp_stable_domain_answers_refine]) assumption

ML \<open>
val checked = [@{thm lp_answer_contract_transition_refinement}, @{thm lpp_stable_domain_answers_refine},
  @{thm lpp_stable_contract_from_finite}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted stable contract refinement dependency" else ();
\<close>
end
