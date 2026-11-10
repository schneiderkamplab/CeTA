theory LP_Cut_Domain_Return_Environments
  imports Category_LP_Cut_Return_Bridge.LP_Cut_Domain_Return_Module_Triples
begin

text \<open>A successful return from a domain-valued input has a domain-valued
answer environment. Continuation proofs use this invariant of actual source
executions, not an assumption about arbitrary residual answers.\<close>

context cut_runtime_domain
begin

definition precise_environments where
  "precise_environments ss \<longleftrightarrow> (\<forall>e eta. (e,eta)\<in>set ss \<longrightarrow> (\<forall>x. D (eta x)))"

lemma precise_environments_prune:
  "precise_environments ss \<Longrightarrow> precise_environments (lpc_answer_prune m ss)"
  by (induct ss) (auto simp: precise_environments_def split: prod.splits lp_cut_entry.splits if_splits)

lemma precise_environments_step:
  assumes step: "precise_answer_transition P ss event tt"
    and domains: "precise_environments ss"
  shows "precise_environments tt"
  using step domains
proof (induct rule: precise_answer_transition.induct)
  case (cut m gs eta es)
  have tail: "precise_environments es" using cut.prems by (auto simp: precise_environments_def)
  have pruned: "precise_environments (lpc_answer_prune m es)"
    by (rule precise_environments_prune[OF tail])
  show ?case using cut.prems pruned by (auto simp: precise_environments_def)
qed (auto simp: precise_environments_def mgu_resolve_def mgu_unify_def intro: substitute)

lemma precise_environments_path:
  "(ss,tt)\<in>(precise_answer_steps P)\<^sup>* \<Longrightarrow>
    precise_environments ss \<Longrightarrow> precise_environments tt"
  by (induct rule: rtrancl_induct)
    (auto simp: precise_answer_steps_def intro: precise_environments_step)

lemma precise_environments_eval:
  "(\<And>x. D (eta x)) \<Longrightarrow> precise_environments (lpc_return_eval eta ss)"
  by (auto simp: precise_environments_def lpc_return_eval_def
    intro: precise_return_env_domain)

lemma precise_returned_domain:
  assumes initial: "precise_environments ss"
    and path: "(ss,us)\<in>(precise_answer_steps P)\<^sup>*"
    and returned: "precise_answer_transition P us (Some rho) tail"
  shows "D (rho x)"
  using precise_environments_path[OF path initial]
    precise_answer_event_is_success[OF returned]
  by (auto simp: precise_environments_def)

end
end
