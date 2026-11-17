theory TRS_Properties
  imports Category_Specifications.TRS_Spec_Base Rewriting_Sequences_Properties
begin
text \<open>Signature correctness is preserved by the two shared term operations.\<close>
lemma correct_subst_term:
  "arity_correct A t \<Longrightarrow> correct_substitution A sigma \<Longrightarrow>
    arity_correct A (fo_subst sigma t)"
  by (induct t) (auto simp: correct_substitution_def list_all_iff)
lemma correct_plug_term:
  "correct_context A C \<Longrightarrow> arity_correct A t \<Longrightarrow>
    arity_correct A (fo_plug C t)"
  by (induct C) (auto simp: list_all_iff)
text \<open>Problem validity gives correct rule sides. Substitution and plugging
then give correct endpoints for any strategy using such rule instances.\<close>
lemma trs_problem_arity_correct:
  assumes "trs_problem A R" "(l,r) \<in> R"
  shows "arity_correct A l" "arity_correct A r"
  using assms by (auto simp: trs_problem_def)

lemma trs_problem_instance_arity_correct:
  assumes "trs_problem A R" "(l,r) \<in> R"
    "correct_substitution A sigma" "correct_context A C"
  shows "arity_correct A (fo_plug C (fo_subst sigma l))"
    "arity_correct A (fo_plug C (fo_subst sigma r))"
  using trs_problem_arity_correct[OF assms(1,2)] assms(3,4)
  by (auto intro: correct_plug_term correct_subst_term)
end
