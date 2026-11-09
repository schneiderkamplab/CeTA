theory TRS_Outermost_Spec
  imports TRS_Spec_Base Rewriting_Sequences_Spec
begin
text \<open>Outermost uses the same finite, signature-correct rule pairs and
infinite variable type as Standard. There is no left-linearity condition,
variable-left-side prohibition, or right-variable restriction.\<close>
definition outermost_root_redex :: "'f ranked_signature \<Rightarrow>
  (('f,'v) fo_term \<times> ('f,'v) fo_term) set \<Rightarrow>
  ('f,'v) fo_term \<Rightarrow> bool" where
  "outermost_root_redex A R t \<longleftrightarrow>
    (\<exists>l r sigma. (l,r) \<in> R \<and> correct_substitution A sigma \<and>
      t = fo_subst sigma l)"

text \<open>Every node strictly above the selected hole must fail to match a
rule left side. The hole itself may be a redex, as may other branches.
This imposes neither a left-to-right order nor a fairness condition.\<close>
fun outermost_above where
  "outermost_above A R SHole u = True"
| "outermost_above A R (SMore f ls C rs) u =
    (\<not> outermost_root_redex A R (fo_plug (SMore f ls C rs) u) \<and>
      outermost_above A R C u)"
definition outermost_step where
  "outermost_step A R s t \<longleftrightarrow>
    arity_correct A s \<and> arity_correct A t \<and>
    (\<exists>l r C sigma. (l,r) \<in> R \<and> correct_context A C \<and>
      correct_substitution A sigma \<and> outermost_above A R C (fo_subst sigma l) \<and>
      s = fo_plug C (fo_subst sigma l) \<and>
      t = fo_plug C (fo_subst sigma r))"
text \<open>Termination means that every outermost sequence on arbitrary
signature-correct terms is finite; open terms are included even if the
signature has no constants. Input validity remains trs_problem.\<close>
definition trs_outermost_terminates where
  "trs_outermost_terminates A R \<longleftrightarrow> no_infinite_steps (outermost_step A R)"
end
