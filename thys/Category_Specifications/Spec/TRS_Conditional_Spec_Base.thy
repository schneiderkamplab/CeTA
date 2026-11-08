theory TRS_Conditional_Spec_Base
  imports TRS_Spec_Base Rewriting_Sequences_Spec
begin

text \<open>An oriented conditional rule has a left side, a right side and an
ordered list of reachability conditions. All terms, substitutions and contexts
are the shared first-order objects; no second term language is introduced.\<close>
type_synonym ('f,'v) conditional_rule =
  "(('f,'v) standard_term \<times> ('f,'v) standard_term) \<times>
    (('f,'v) standard_term \<times> ('f,'v) standard_term) list"

definition conditional_problem ::
  "'f ranked_signature \<Rightarrow> ('f,'v) conditional_rule set \<Rightarrow> bool" where
  "conditional_problem A R \<longleftrightarrow>
    infinite (UNIV :: 'v set) \<and> finite R \<and>
    (\<forall>((l,r),cs)\<in>R. arity_correct A l \<and> arity_correct A r \<and>
      (\<forall>(s,t)\<in>set cs. arity_correct A s \<and> arity_correct A t))"

text \<open>A goal asks for one rewrite or for a finite, possibly empty sequence.
The inference rules below describe proof attempts, including unsuccessful ones.
Premises are evaluated in their displayed order.\<close>
datatype ('f,'v) conditional_goal =
    CRewrite "('f,'v) standard_term" "('f,'v) standard_term"
  | CReach "('f,'v) standard_term" "('f,'v) standard_term"

inductive conditional_inference for A R where
  reflexive: "arity_correct A s \<Longrightarrow> conditional_inference A R (CReach s s) []"
| transitive: "arity_correct A s \<Longrightarrow> arity_correct A u \<Longrightarrow> arity_correct A t \<Longrightarrow>
    conditional_inference A R (CReach s t) [CRewrite s u, CReach u t]"
| rule: "((l,r),cs) \<in> R \<Longrightarrow> correct_context A C \<Longrightarrow>
    correct_substitution A sigma \<Longrightarrow>
    arity_correct A (standard_plug C (standard_subst sigma l)) \<Longrightarrow>
    arity_correct A (standard_plug C (standard_subst sigma r)) \<Longrightarrow>
    (\<forall>(s,t)\<in>set cs. arity_correct A (standard_subst sigma s) \<and>
      arity_correct A (standard_subst sigma t)) \<Longrightarrow>
    conditional_inference A R
      (CRewrite (standard_plug C (standard_subst sigma l))
                (standard_plug C (standard_subst sigma r)))
      (map (\<lambda>(s,t). CReach (standard_subst sigma s) (standard_subst sigma t)) cs)"

text \<open>Success requires a finite proof of every premise. This least
inductive definition cannot justify a rule by circular condition evaluation.\<close>
inductive conditional_success for A R where
  derive: "conditional_inference A R g gs \<Longrightarrow>
    list_all (conditional_success A R) gs \<Longrightarrow> conditional_success A R g"

definition conditional_step where
  "conditional_step A R s t \<longleftrightarrow> conditional_success A R (CRewrite s t)"

text \<open>An evaluation descends to a premise only after all its earlier
siblings have succeeded. The selected premise need not succeed. This records
infinite left-to-right proof attempts, not only completed rewrite steps.\<close>
definition conditional_evaluation_step where
  "conditional_evaluation_step A R g h \<longleftrightarrow>
    (\<exists>gs i. conditional_inference A R g gs \<and> i < length gs \<and>
      (\<forall>j<i. conditional_success A R (gs!j)) \<and> h = gs!i)"


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
