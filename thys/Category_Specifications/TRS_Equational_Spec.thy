theory TRS_Equational_Spec
  imports TRS_Spec_Base Rewriting_Sequences_Spec
begin
text \<open>The input is a finite ranked rewrite system with two finite sets of
binary symbols. Membership in the first declares associativity; membership in
the second declares commutativity. A symbol may belong to both. Terms may be
open, and no variable restriction is imposed on rewrite rules.\<close>
definition equational_problem where
  "equational_problem A R FA FC \<longleftrightarrow> trs_problem A R \<and>
    finite FA \<and> finite FC \<and> (\<forall>f\<in>FA \<union> FC. A f = Some 2)"

text \<open>These are all instances of the declared equations, in both
directions. The set ranges over terms s, t and u; it is generally infinite
even when the declared symbol sets are finite. These are equation instances,
not a finite rule schema or additional input rewrite rules.
Context closure and signature correctness use the shared rewrite definition.\<close>
definition equational_axioms where
  "equational_axioms FA FC =
    {(SFun f [SFun f [s,t],u], SFun f [s,SFun f [t,u]]) | f s t u. f\<in>FA} \<union>
    {(SFun f [s,SFun f [t,u]], SFun f [SFun f [s,t],u]) | f s t u. f\<in>FA} \<union>
    {(SFun f [s,t], SFun f [t,s]) | f s t. f\<in>FC}"
definition equational_conversion where
  "equational_conversion A FA FC s t \<longleftrightarrow>
    finite_steps (fo_step A (equational_axioms FA FC)) s t"

text \<open>One step modulo the theory contains exactly one rewrite step,
preceded and followed by finite equational conversions. An infinite sequence
of equation changes alone does not violate termination.\<close>
definition equational_step where
  "equational_step A R FA FC s t \<longleftrightarrow>
    (\<exists>u v. equational_conversion A FA FC s u \<and>
      fo_step A R u v \<and> equational_conversion A FA FC v t)"
definition trs_equational_terminates where
  "trs_equational_terminates A R FA FC \<longleftrightarrow>
    no_infinite_steps (equational_step A R FA FC)"
end
