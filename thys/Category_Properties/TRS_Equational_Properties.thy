theory TRS_Equational_Properties
  imports Category_Specifications.TRS_Equational_Spec
    TRS_Properties
begin

lemma trs_equational_nontermination_iff:
  "\<not> trs_equational_terminates A R FA FC \<longleftrightarrow>
    (\<exists>ts. \<forall>i. equational_step A R FA FC (ts i) (ts (Suc i)))"
  by (simp add: trs_equational_terminates_def no_infinite_steps_def)
end
