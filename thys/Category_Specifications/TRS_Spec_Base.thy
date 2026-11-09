theory TRS_Spec_Base
  imports Main
begin

text \<open>The prefix fo means first-order and is shared by all TRS categories.
Finite first-order terms over a variable type. The problem-validity predicate below requires
that type to be infinite. A signature assigns each permitted symbol exactly one arity; None
excludes a symbol. Neither the signature nor the terms need contain constants.\<close>
datatype ('f, 'v) fo_term = SVar 'v | SFun 'f "('f, 'v) fo_term list"
type_synonym 'f ranked_signature = "'f \<Rightarrow> nat option"

fun arity_correct :: "'f ranked_signature \<Rightarrow> ('f, 'v) fo_term \<Rightarrow> bool" where
  "arity_correct A (SVar x) = True"
| "arity_correct A (SFun f ts) = (A f = Some (length ts) \<and> list_all (arity_correct A) ts)"

text \<open>A substitution replaces variables simultaneously by finite terms. Its
images may themselves contain variables. Signature correctness is global.\<close>
fun fo_subst :: "('v \<Rightarrow> ('f, 'v) fo_term) \<Rightarrow> ('f, 'v) fo_term \<Rightarrow> ('f, 'v) fo_term" where
  "fo_subst s (SVar x) = s x"
| "fo_subst s (SFun f ts) = SFun f (map (fo_subst s) ts)"
definition correct_substitution where
  "correct_substitution A s \<longleftrightarrow> (\<forall>x. arity_correct A (s x))"

text \<open>A context contains exactly one hole. The lists contain its left and
right siblings. Plugging fills the hole, at any depth.\<close>
datatype ('f, 'v) fo_context = SHole
  | SMore 'f "('f, 'v) fo_term list" "('f, 'v) fo_context" "('f, 'v) fo_term list"
fun fo_plug where
  "fo_plug SHole t = t"
| "fo_plug (SMore f ls C rs) t = SFun f (ls @ fo_plug C t # rs)"
fun correct_context where
  "correct_context A SHole = True"
| "correct_context A (SMore f ls C rs) =
    (A f = Some (length ls + 1 + length rs) \<and>
     list_all (arity_correct A) ls \<and> correct_context A C \<and>
     list_all (arity_correct A) rs)"

text \<open>A problem consists of finitely many signature-correct pairs. In
particular, variable left sides and extra right-side variables are not excluded.\<close>
definition trs_problem ::
  "'f ranked_signature \<Rightarrow> (('f,'v) fo_term \<times> ('f,'v) fo_term) set \<Rightarrow> bool"
where
  "trs_problem A R \<longleftrightarrow> infinite (UNIV :: 'v set) \<and> finite R \<and>
    (\<forall>(l,r)\<in>R. arity_correct A l \<and> arity_correct A r)"

text \<open>A rewrite step is a rule instance in an arbitrary signature-correct
context. Both endpoints and all substitution images respect the signature.\<close>
definition fo_step where
  "fo_step A R s t \<longleftrightarrow>
    arity_correct A s \<and> arity_correct A t \<and>
    (\<exists>l r C sigma. (l,r) \<in> R \<and> correct_context A C \<and>
      correct_substitution A sigma \<and>
      s = fo_plug C (fo_subst sigma l) \<and>
      t = fo_plug C (fo_subst sigma r))"

end
