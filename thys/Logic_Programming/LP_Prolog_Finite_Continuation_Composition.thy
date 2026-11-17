theory LP_Prolog_Finite_Continuation_Composition
 imports LP_Prolog_Domain_Invariant_Composition LP_Prolog_Finite_Matching_Head
begin

fun lpp_finite_execution_entry where
 "lpp_finite_execution_entry (LPCGoals gs) = lpp_finite_goals gs"
| "lpp_finite_execution_entry (LPCClause gs c m) = lpp_finite_goals gs"
| "lpp_finite_execution_entry (LPCBarrier m) = True"

definition lpp_finite_execution where
 "lpp_finite_execution ss = list_all (\<lambda>frame. lpp_finite_execution_entry (fst frame)) ss"

lemma lpp_finite_attached_tail:
 "lpp_finite_execution (lpc_attach_answers rest ((LPCGoals [],eta)#ss)) \<Longrightarrow>
  lpp_finite_execution (lpc_attach_answers rest ss)"
 by (simp add: lpp_finite_execution_def lpc_attach_answers_def)

lemma lpp_finite_attached_continuation:
 "lpp_finite_execution (lpc_attach_answers rest ((LPCGoals [],eta)#ss)) \<Longrightarrow>
  lpp_finite_goals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest)"
 by (simp add: lpp_finite_execution_def lpc_attach_answers_def)

theorem lpp_domain_contract_compose_finite_continuation:
 assumes program: "lp_cut_source_program P"
 and prefix: "lp_answer_contract (lpp_domain_answers P B U D) ss R t ret"
 and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
 and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss)) = {}"
 and initial: "lpp_finite_execution (lpc_attach_answers rest ss)"
 and preserve: "\<And>us ev vs. lpp_finite_execution (lpc_attach_answers rest us) \<Longrightarrow>
   (ss,us)\<in>(lp_answer_steps (lpp_domain_answers P B U D))\<^sup>* \<Longrightarrow>
   lpc_prefix_active us \<Longrightarrow>
   lpp_domain_answers P B U D (lpc_attach_answers rest us) ev (lpc_attach_answers rest vs) \<Longrightarrow>
   lpp_finite_execution (lpc_attach_answers rest vs)"
 and continuation: "\<And>eta. lp_actual_answer (lpp_domain_answers P B U D) ss eta \<Longrightarrow>
   lpp_finite_goals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest) \<Longrightarrow>
   lp_answer_contract (lpp_domain_answers P B U D)
     [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] R (ret eta) final"
 shows "lp_answer_contract (lpp_domain_answers P B U D) (lpc_attach_answers rest ss) R t final"
proof (rule lpp_domain_contract_compose_actual_invariant[where
 I="\<lambda>us. lpp_finite_execution (lpc_attach_answers rest us)",
 OF program prefix valid separated initial preserve lpp_finite_attached_tail])
 fix eta vs
 assume actual: "lp_actual_answer (lpp_domain_answers P B U D) ss eta"
 and finite: "lpp_finite_execution (lpc_attach_answers rest ((LPCGoals [],eta)#vs))"
 show "lp_answer_contract (lpp_domain_answers P B U D)
   [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] R (ret eta) final"
   by (rule continuation[OF actual lpp_finite_attached_continuation[OF finite]])
qed

ML \<open>
val checked = @{thms lpp_domain_contract_compose_finite_continuation};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted finite continuation composition" else ();
\<close>
end
