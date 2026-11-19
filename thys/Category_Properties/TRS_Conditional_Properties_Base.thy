theory TRS_Conditional_Properties_Base
  imports Category_Specifications.TRS_Conditional_Spec_Base
    TRS_Properties
begin

fun conditional_goal_correct where
  "conditional_goal_correct A (CRewrite s t) = (arity_correct A s \<and> arity_correct A t)"
| "conditional_goal_correct A (CReach s t) = (arity_correct A s \<and> arity_correct A t)"
lemma conditional_inference_correct:
  "conditional_inference A R g gs \<Longrightarrow> conditional_goal_correct A g"
  by (erule conditional_inference.cases) auto
lemma conditional_success_correct:
  "conditional_success A R g \<Longrightarrow> conditional_goal_correct A g"
  by (erule conditional_success.cases) (blast intro: conditional_inference_correct)
lemma conditional_step_correct:
  "conditional_step A R s t \<Longrightarrow> arity_correct A s \<and> arity_correct A t"
  using conditional_success_correct[of A R "CRewrite s t"]
  by (simp add: conditional_step_def)
end
