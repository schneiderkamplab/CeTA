theory TRS_Conditional_Operational_Properties
  imports Category_Specifications.TRS_Conditional_Operational_Spec
    TRS_Conditional_Ordinary_Properties
begin

lemma trs_conditional_operational_nontermination_iff:
  "\<not> trs_conditional_operationally_terminates A R \<longleftrightarrow>
    (\<exists>gs. \<forall>i. conditional_evaluation_step A R (gs i) (gs (Suc i)))"
  by (simp add: trs_conditional_operationally_terminates_def no_infinite_steps_def)

text \<open>Every infinite rewrite sequence induces an infinite proof attempt:
after each successful first premise of transitivity, continue with its second.\<close>
theorem operational_implies_ordinary:
  assumes "trs_conditional_operationally_terminates A R"
  shows "trs_conditional_terminates A R"
proof (rule ccontr)
  assume "\<not> trs_conditional_terminates A R"
  then obtain ts where steps: "\<And>i. conditional_step A R (ts i) (ts (Suc i))"
    by (auto simp: trs_conditional_nontermination_iff)
  have wf: "arity_correct A (ts i)" for i using conditional_step_correct[OF steps[of i]] by simp
  have edge: "conditional_evaluation_step A R (CReach (ts i) (ts 0))
      (CReach (ts (Suc i)) (ts 0))" for i
    unfolding conditional_evaluation_step_def
    by (intro exI[of _ "[CRewrite (ts i) (ts (Suc i)), CReach (ts (Suc i)) (ts 0)]"]
      exI[of _ 1] conjI; (rule conditional_inference.transitive[OF wf wf wf] |
        simp add: conditional_step_def[symmetric] steps less_Suc_eq))
  have "\<not> trs_conditional_operationally_terminates A R"
    unfolding trs_conditional_operational_nontermination_iff
    by (intro exI[of _ "\<lambda>i. CReach (ts i) (ts 0)"] allI edge)
  with assms show False by contradiction
qed
end
