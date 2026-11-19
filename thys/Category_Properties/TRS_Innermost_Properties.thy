theory TRS_Innermost_Properties
  imports Category_Specifications.TRS_Innermost_Spec
    TRS_Properties
begin

lemma innermost_step_arity_correct:
  assumes "trs_problem A R" "innermost_step A R s t"
  shows "arity_correct A s" "arity_correct A t"
  using assms(2) trs_problem_instance_arity_correct[OF assms(1)]
  unfolding innermost_step_def by blast+

lemma trs_innermost_nontermination_iff:
  "\<not> trs_innermost_terminates A R \<longleftrightarrow>
    (\<exists>ts. \<forall>i. innermost_step A R (ts i) (ts (Suc i)))"
  by (simp add: trs_innermost_terminates_def no_infinite_steps_def)
end
