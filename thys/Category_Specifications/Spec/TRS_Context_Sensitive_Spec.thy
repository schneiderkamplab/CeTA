theory TRS_Context_Sensitive_Spec
  imports TRS_Spec_Base Rewriting_Sequences_Spec
begin
text \<open>The replacement map assigns permitted argument indices to each
symbol and arity. Indices start at zero. The root is always permitted; a
nested occurrence is permitted only if every edge leading to it is permitted.\<close>
fun permitted_context :: "('f \<times> nat \<Rightarrow> nat set) \<Rightarrow> ('f,'v) standard_context \<Rightarrow> bool" where
  "permitted_context mu SHole = True"
| "permitted_context mu (SMore f before C after) =
    (length before \<in> mu (f,Suc (length before + length after)) \<and> permitted_context mu C)"
text \<open>A context-sensitive step is a signature-correct rule instance in a
permitted context. Replacement-map entries outside a symbol's arity cannot
select an occurrence and have no effect.\<close>
definition context_sensitive_step where
  "context_sensitive_step A mu R s t \<longleftrightarrow>
    arity_correct A s \<and> arity_correct A t \<and>
    (\<exists>l r C sigma. (l,r) \<in> R \<and> correct_context A C \<and>
      permitted_context mu C \<and> correct_substitution A sigma \<and>
      s = standard_plug C (standard_subst sigma l) \<and>
      t = standard_plug C (standard_subst sigma r))"
definition trs_context_sensitive_terminates where
  "trs_context_sensitive_terminates A mu R \<longleftrightarrow>
    no_infinite_steps (context_sensitive_step A mu R)"
lemma trs_context_sensitive_nontermination_iff:
  "\<not> trs_context_sensitive_terminates A mu R \<longleftrightarrow>
    (\<exists>ts. \<forall>i. context_sensitive_step A mu R (ts i) (ts (Suc i)))"
  by (simp add: trs_context_sensitive_terminates_def infinite_steps_iff)
end
