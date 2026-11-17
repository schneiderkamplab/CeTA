theory LP_Prolog_Domain_Invariant_Composition
 imports LP_Prolog_Domain_Composition LP_Scoped_Answer_Invariant_Composition
begin

theorem lpp_domain_contract_compose_actual_invariant:
  assumes program: "lp_cut_source_program P"
    and prefix: "lp_answer_contract (lpp_domain_answers P B U D) ss R t ret"
    and valid: "list_all (\<lambda>x. lpc_clause_nonempty (fst x)) ss"
    and separated: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst ss)) = {}"
    and initial: "I ss"
    and invariant_step: "\<And>us ev vs. I us \<Longrightarrow>
      (ss,us)\<in>(lp_answer_steps (lpp_domain_answers P B U D))\<^sup>* \<Longrightarrow>
      lpc_prefix_active us \<Longrightarrow>
      lpp_domain_answers P B U D (lpc_attach_answers rest us) ev (lpc_attach_answers rest vs) \<Longrightarrow> I vs"
    and invariant_tail: "\<And>eta vs. I ((LPCGoals [],eta)#vs) \<Longrightarrow> I vs"
    and continuation: "\<And>eta vs. lp_actual_answer (lpp_domain_answers P B U D) ss eta \<Longrightarrow>
      I ((LPCGoals [],eta)#vs) \<Longrightarrow> lp_answer_contract (lpp_domain_answers P B U D)
        [(LPCGoals (map (lp_cut_map (\<lambda>x. lp_ieval x eta)) rest),eta)] R (ret eta) final"
  shows "lp_answer_contract (lpp_domain_answers P B U D) (lpc_attach_answers rest ss) R t final"
proof (rule lp_scoped_answer_contract_compose_actual_invariant[where I=I and rest=rest, OF prefix valid separated initial invariant_step invariant_tail continuation])
  show "\<And>us ev vs. lpp_domain_answers P B U D us ev vs \<Longrightarrow>
    list_all (\<lambda>x. lpc_clause_nonempty (fst x)) us \<Longrightarrow>
    list_all (\<lambda>x. lpc_clause_nonempty (fst x)) vs"
    by (auto simp: lpp_domain_answers_def dest: lpp_clause_nonempty_preserved)
  show "\<And>us ev result. lpc_prefix_active us \<Longrightarrow>
    lpp_domain_answers P B U D (lpc_attach_answers rest us) ev result \<Longrightarrow>
    ev = None \<and> (\<exists>vs. lpp_domain_answers P B U D us None vs \<and> result = lpc_attach_answers rest vs)"
    by (rule lpp_domain_attach_reflect)
  show "\<And>us ev vs. lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst us)) = {} \<Longrightarrow>
    lpp_domain_answers P B U D (lpc_attach_answers rest us) ev (lpc_attach_answers rest vs) \<Longrightarrow>
    lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst vs)) = {}"
  proof -
    fix us ev vs
    assume sep: "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst us)) = {}"
      and step: "lpp_domain_answers P B U D (lpc_attach_answers rest us) ev (lpc_attach_answers rest vs)"
    show "lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst vs)) = {}"
    proof (cases "lpp_answer_transition P B U (lpc_attach_answers rest us) ev (lpc_attach_answers rest vs)")
      case True
      have source: "(lpc_attach rest us,lpc_attach rest vs)\<in>lpp_atomic_source P B U"
        using lpp_answer_transition_erases[OF True] by (simp add: lpc_attach_answers_erases)
      show ?thesis using lpp_attach_barriers_preserved[OF sep source] by (simp add: lpc_attach_barriers)
    next
      case False
      have eq: "lpc_attach_answers rest vs = lpc_attach_answers rest us"
        using step False by (simp add: lpp_domain_answers_def)
      have "lpc_barrier_ids (map fst vs) = lpc_barrier_ids (map fst us)"
        using arg_cong[OF eq, of "\<lambda>xs. lpc_barrier_ids (map fst xs)"]
        by (simp add: lpc_attach_answers_erases lpc_attach_barriers)
      then show ?thesis using sep by simp
    qed
  qed
  show "\<And>ev vs. \<not>lpp_domain_answers P B U D [] ev vs"
    by (auto simp: lpp_domain_answers_def elim: lpp_answer_transition.cases lpc_answer_transition.cases)
  show "\<And>eta vs. lpp_domain_answers P B U D ((LPCGoals [],eta)#vs) (Some eta) vs"
    by (auto simp: lpp_domain_answers_def lpp_builtin_active_def
      intro: lpp_answer_transition.base lpc_answer_transition.success)
  show "\<And>us vs. lpc_owned_stack (lpc_rest_scopes rest) (map fst us) \<Longrightarrow>
    lpc_rest_scopes rest \<inter> set (lpc_barrier_ids (map fst vs)) = {} \<Longrightarrow>
    lp_answer_contract (lpp_domain_answers P B U D) us R t final \<Longrightarrow>
    lp_answer_contract (lpp_domain_answers P B U D) vs R t final \<Longrightarrow>
    lp_answer_contract (lpp_domain_answers P B U D) (us@vs) R t final"
    by (rule lpp_domain_owned_append[OF program])
qed

ML \<open>
val checked = @{thms lpp_domain_contract_compose_actual_invariant};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted domain invariant composition" else ();
\<close>
end
