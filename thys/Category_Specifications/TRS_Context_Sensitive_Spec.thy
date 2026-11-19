theory TRS_Context_Sensitive_Spec
  imports TRS_Spec_Base Rewriting_Sequences_Spec
begin
text \<open>The replacement map assigns permitted argument indices to each
symbol. Indices start at zero. The root is always permitted; a
nested occurrence is permitted only if every edge leading to it is permitted.\<close>
fun permitted_context :: "('f \<Rightarrow> nat set) \<Rightarrow> ('f,'v) fo_context \<Rightarrow> bool" where
  "permitted_context mu SHole = True"
| "permitted_context mu (SMore f ls C rs) =
    (length ls \<in> mu f \<and> permitted_context mu C)"
text \<open>A context-sensitive step is a signature-correct rule instance in a
permitted context. Replacement-map entries outside a symbol's arity cannot
select an occurrence and have no effect.\<close>
definition context_sensitive_step ::
  "'f arity \<Rightarrow> ('f \<Rightarrow> nat set) \<Rightarrow> ('f,'v) rewriting_rules \<Rightarrow>
    ('f, 'v) fo_term \<Rightarrow> ('f, 'v) fo_term \<Rightarrow> bool" where
  "context_sensitive_step A mu R s t \<longleftrightarrow>
    (\<exists>l r C sigma. (l,r) \<in> R \<and> correct_context A C \<and>
      permitted_context mu C \<and> correct_substitution A sigma \<and>
      s = fo_plug C (fo_subst sigma l) \<and>
      t = fo_plug C (fo_subst sigma r))"
definition trs_context_sensitive_terminates ::
  "'f arity \<Rightarrow> ('f \<Rightarrow> nat set) \<Rightarrow> ('f,'v) rewriting_rules \<Rightarrow>
    bool" where
  "trs_context_sensitive_terminates A mu R \<longleftrightarrow>
    no_infinite_steps (context_sensitive_step A mu R)"
end
