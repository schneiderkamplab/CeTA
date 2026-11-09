theory TRS_Innermost_Spec
  imports TRS_Spec_Base Rewriting_Sequences_Spec
begin

text \<open>We use the same finite terms, ranked signatures, substitutions,
contexts and valid problems as TRS Standard. In particular, variables range
over an infinite type, rules are finite and signature-correct, and neither
variable left sides nor extra right-side variables are excluded.\<close>

text \<open>A term is irreducible when no rule left side can be instantiated
anywhere inside it. Matching and the surrounding context respect the signature.
For valid problems this is exactly absence of an ordinary rewrite step.\<close>
definition innermost_normal :: "'f ranked_signature \<Rightarrow>
  (('f,'v) fo_term \<times> ('f,'v) fo_term) set \<Rightarrow>
  ('f,'v) fo_term \<Rightarrow> bool" where
  "innermost_normal A R t \<longleftrightarrow>
    \<not> (\<exists>l r C sigma. (l,r) \<in> R \<and> correct_context A C \<and>
      correct_substitution A sigma \<and>
      t = fo_plug C (fo_subst sigma l))"

text \<open>The proper subterms exclude the term itself and include all
subterms of its immediate arguments. A variable has no proper subterms.\<close>
fun proper_subterms where
  "proper_subterms (SVar x) = {}"
| "proper_subterms (SFun f ts) = set ts \<union> \<Union>(proper_subterms ` set ts)"

text \<open>An innermost step contracts a rule instance whose every proper
subterm is irreducible. The surrounding context is arbitrary: another branch
may still contain redexes. This imposes no left-to-right evaluation order.\<close>
definition innermost_step where
  "innermost_step A R s t \<longleftrightarrow>
    arity_correct A s \<and> arity_correct A t \<and>
    (\<exists>l r C sigma. (l,r) \<in> R \<and> correct_context A C \<and>
      correct_substitution A sigma \<and>
      (\<forall>u\<in>proper_subterms (fo_subst sigma l). innermost_normal A R u) \<and>
      s = fo_plug C (fo_subst sigma l) \<and>
      t = fo_plug C (fo_subst sigma r))"

text \<open>Ranked TRS Innermost termination is absence of an infinite sequence
of innermost steps, on arbitrary terms rather than only ground terms. As for
Standard, input validity is the separate predicate trs_problem.\<close>
definition trs_innermost_terminates where
  "trs_innermost_terminates A R \<longleftrightarrow>
    no_infinite_steps (innermost_step A R)"
end
