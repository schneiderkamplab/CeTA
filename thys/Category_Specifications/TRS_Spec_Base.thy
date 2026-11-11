theory TRS_Spec_Base
  imports First_Order_Terms_Spec
begin

text \<open>A ranked signature is a partial arity function: Some n admits a symbol
with arity n, while None excludes it. In particular, Some 0 admits a constant;
None does not. The empty signature and signatures without constants are allowed.
The shared raw term operations are restricted here to this signature.\<close>
type_synonym 'f ranked_signature = "'f \<Rightarrow> nat option"

fun arity_correct :: "'f ranked_signature \<Rightarrow> ('f, 'v) fo_term \<Rightarrow> bool" where
  "arity_correct A (SVar x) = True"
| "arity_correct A (SFun f ts) = (A f = Some (length ts) \<and> list_all (arity_correct A) ts)"

text \<open>A correct substitution maps every variable to a signature-correct term.\<close>
definition correct_substitution where
  "correct_substitution A s \<longleftrightarrow> (\<forall>x. arity_correct A (s x))"

text \<open>A correct context respects the signature at every node outside its hole.\<close>
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
