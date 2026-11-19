theory Rewriting_Sequences_Properties
  imports Category_Specifications.Rewriting_Sequences_Spec
begin

lemma infinite_steps_iff:
  "\<not> no_infinite_steps step \<longleftrightarrow> (\<exists>ts. \<forall>i. step (ts i) (ts (Suc i)))"
  by (simp add: no_infinite_steps_def)
end
