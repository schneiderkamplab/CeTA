theory TRS_Context_Sensitive_Examples
  imports TRS_Context_Sensitive_Properties TRS_Standard_Examples
begin
lemma all_contexts_permitted: "permitted_context (\<lambda>_. UNIV) C"
  by (induct C) auto
lemma full_map_is_standard:
  "context_sensitive_step A (\<lambda>_. UNIV) R s t \<longleftrightarrow> fo_step A R s t"
  unfolding context_sensitive_step_def fo_step_def
  using all_contexts_permitted by blast
lemma full_map_termination:
  "trs_context_sensitive_terminates A (\<lambda>_. UNIV) R \<longleftrightarrow> trs_standard_terminates A R"
  by (simp add: trs_context_sensitive_terminates_def trs_standard_terminates_def no_infinite_steps_def
      no_infinite_steps_def full_map_is_standard)
lemma frozen_context:
  "permitted_context (\<lambda>_. {}) C \<longleftrightarrow> C = SHole"
  by (cases C) auto
lemma frozen_argument:
  "\<not> context_sensitive_step (\<lambda>_. Some 1) (\<lambda>_. {})
    {(SFun False [SVar (0::nat)],SVar 0)}
    (SFun True [SFun False [SVar 7]]) (SFun True [SVar 7])"
  by (simp add: context_sensitive_step_def frozen_context)
lemma root_allowed_when_frozen:
  "context_sensitive_step unary (\<lambda>_. {})
    {(SFun () [SVar (0::nat)],SVar 0)} (SFun () [SVar 7]) (SVar 7)"
  unfolding context_sensitive_step_def
  apply (intro conjI)
    apply (simp add: unary_def)
   apply simp
  apply (rule exI[of _ "SFun () [SVar (0::nat)]"], rule exI[of _ "SVar (0::nat)"])
  apply (rule exI[of _ SHole], rule exI[of _ "\<lambda>_. SVar (7::nat)"])
  by (simp add: correct_substitution_def)
lemma csr_below_root_nonground:
  "context_sensitive_step unary (\<lambda>_. UNIV)
    {(SFun () [SVar (0::nat)],SVar 0)}
    (SFun () [SFun () [SVar 7]]) (SFun () [SVar 7])"
  by (simp add: full_map_is_standard below_root_nonground)
lemma csr_empty: "trs_context_sensitive_terminates A mu {}"
  by (simp add: trs_context_sensitive_terminates_def no_infinite_steps_def context_sensitive_step_def)
lemma csr_arity_mismatch:
  "\<not> context_sensitive_step unary mu R (SFun () []) t"
  by (simp add: context_sensitive_step_def unary_def)
lemma csr_variable_self_loop:
  "\<not> trs_context_sensitive_terminates A mu {(SVar (0::nat), SVar 0)}"
proof -
  have step: "context_sensitive_step A mu {(SVar (0::nat), SVar 0)} (SVar 0) (SVar 0)"
    unfolding context_sensitive_step_def
    apply (intro conjI)
      apply simp
     apply simp
    apply (rule exI[of _ "SVar (0::nat)"], rule exI[of _ "SVar (0::nat)"])
    apply (rule exI[of _ SHole], rule exI[of _ "\<lambda>_. SVar (0::nat)"])
    by (simp add: correct_substitution_def)
  have "\<exists>ts. \<forall>i. context_sensitive_step A mu {(SVar (0::nat), SVar 0)} (ts i) (ts (Suc i))"
    by (rule exI[of _ "\<lambda>_. SVar (0::nat)"]) (simp add: step)
  then show ?thesis by (simp add: trs_context_sensitive_nontermination_iff)
qed

end
