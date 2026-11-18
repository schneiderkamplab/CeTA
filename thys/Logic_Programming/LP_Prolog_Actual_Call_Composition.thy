theory LP_Prolog_Actual_Call_Composition
 imports LP_Prolog_Finite_Continuation_Composition
begin

text \<open>Termination and actual-return properties remain separate obligations.
A constant residual return supplies no information about the returned values;
continuation facts must be established for actual answers independently.\<close>

lemma lp_constant_answer_contract:
 "lp_answer_contract T ss R t (\<lambda>_. t) = SN_on (lp_answer_steps T) {ss}"
 by (simp add: lp_answer_contract_def lp_answers_covered_def)

lemma lpp_finite_actual_call_composition:
 assumes program: "lp_cut_source_program P"
 and prefix: "SN_on (lp_answer_steps (lpp_domain_answers P B U D)) {ss}"
 and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
 and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss))={}"
 and initial: "lpp_finite_execution (lpc_attach_answers rest ss)"
 and preserve: "\<And>us ev vs. lpp_finite_execution (lpc_attach_answers rest us) \<Longrightarrow>
   (ss,us)\<in>(lp_answer_steps (lpp_domain_answers P B U D))\<^sup>* \<Longrightarrow>
   lpc_prefix_active us \<Longrightarrow>
   lpp_domain_answers P B U D (lpc_attach_answers rest us) ev (lpc_attach_answers rest vs) \<Longrightarrow>
   lpp_finite_execution (lpc_attach_answers rest vs)"
 and returns: "\<And>rho. lp_actual_answer (lpp_domain_answers P B U D) ss rho \<Longrightarrow> K rho"
 and continuation: "\<And>rho. lp_actual_answer (lpp_domain_answers P B U D) ss rho \<Longrightarrow>
   K rho \<Longrightarrow> lpp_finite_goals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest) \<Longrightarrow>
   SN_on (lp_answer_steps (lpp_domain_answers P B U D))
    {[(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)]}"
 shows "SN_on (lp_answer_steps (lpp_domain_answers P B U D)) {lpc_attach_answers rest ss}"
proof -
 have prefix_contract: "lp_answer_contract (lpp_domain_answers P B U D) ss {} () (\<lambda>_. ())"
  using prefix by (simp add: lp_constant_answer_contract)
 have composed: "lp_answer_contract (lpp_domain_answers P B U D)
   (lpc_attach_answers rest ss) {} () (\<lambda>_. ())"
 proof (rule lpp_domain_contract_compose_finite_continuation[
   OF program prefix_contract valid separated initial preserve])
  fix rho
  assume actual: "lp_actual_answer (lpp_domain_answers P B U D) ss rho"
   and finite: "lpp_finite_goals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest)"
  show "lp_answer_contract (lpp_domain_answers P B U D)
   [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x rho)) rest),rho)] {} () (\<lambda>_. ())"
   using continuation[OF actual returns[OF actual] finite]
   by (simp add: lp_constant_answer_contract)
 qed
 show ?thesis using composed by (simp add: lp_constant_answer_contract)
qed

ML \<open>
val checked = @{thms lp_constant_answer_contract lpp_finite_actual_call_composition};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted actual-call composition" else ();
\<close>
end
