theory TRS_Context_Sensitive_Properties
  imports Category_Specifications.TRS_Context_Sensitive_Spec
    TRS_Properties
begin

lemma trs_context_sensitive_nontermination_iff:
  "\<not> trs_context_sensitive_terminates A mu R \<longleftrightarrow>
    (\<exists>ts. \<forall>i. context_sensitive_step A mu R (ts i) (ts (Suc i)))"
  by (simp add: trs_context_sensitive_terminates_def infinite_steps_iff)
end
