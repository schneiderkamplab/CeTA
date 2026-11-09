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
end
