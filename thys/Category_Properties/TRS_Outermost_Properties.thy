theory TRS_Outermost_Properties
  imports Category_Specifications.TRS_Outermost_Spec
    TRS_Properties
begin

lemma outermost_step_arity_correct:
  assumes "trs_problem A R" "outermost_step A R s t"
  shows "arity_correct A s" "arity_correct A t"
  using assms(2) trs_problem_instance_arity_correct[OF assms(1)]
  unfolding outermost_step_def by blast+

lemma trs_outermost_nontermination_iff:
  "\<not> trs_outermost_terminates A R \<longleftrightarrow>
    (\<exists>ts. \<forall>i. outermost_step A R (ts i) (ts (Suc i)))"
  by (simp add: trs_outermost_terminates_def no_infinite_steps_def)
end
