theory TRS_Equational_Spec
  imports TRS_Spec_Base Rewriting_Sequences_Spec
begin
text \<open>We consider termination of rewriting modulo declared associativity
and commutativity equations. The finite rule set R contains the rewrite rules.
The finite sets FA and FC specify which binary function symbols are associative
and commutative, respectively; a symbol may belong to both. A step consists of
one application of a rewrite rule, preceded and followed by finitely many
applications of the declared equations. Termination excludes infinite sequences
of these steps. Terms may contain variables, and rules may have variable
left-hand sides or extra variables on their right-hand sides.\<close>
definition equational_problem ::
  "'f arity \<Rightarrow> ('f,'v) rewriting_rules \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow>
    bool" where
  "equational_problem A R FA FC \<longleftrightarrow> trs_problem A R \<and>
    finite FA \<and> finite FC \<and> (\<forall>f\<in>FA \<union> FC. A f = 2)"

text \<open>These are all instances of the declared equations, in both
directions. The set ranges over terms s, t and u; it is generally infinite
even when the declared symbol sets are finite. These are equation instances,
not a finite rule schema or additional input rewrite rules.
Context closure and signature correctness use the shared rewrite definition.\<close>
definition equational_axioms ::
  "'f set \<Rightarrow> 'f set \<Rightarrow> ('f,'v) rewriting_rules" where
  "equational_axioms FA FC =
    {(SFun f [SFun f [s,t],u], SFun f [s,SFun f [t,u]]) | f s t u. f\<in>FA} \<union>
    {(SFun f [s,SFun f [t,u]], SFun f [SFun f [s,t],u]) | f s t u. f\<in>FA} \<union>
    {(SFun f [s,t], SFun f [t,s]) | f s t. f\<in>FC}"
definition equational_conversion ::
  "'f arity \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow> ('f, 'v) fo_term \<Rightarrow> ('f,
    'v) fo_term \<Rightarrow> bool" where
  "equational_conversion A FA FC s t \<longleftrightarrow>
    finite_steps (fo_step A (equational_axioms FA FC)) s t"

text \<open>One step modulo the theory contains exactly one rewrite step,
preceded and followed by finite equational conversions. An infinite sequence
of equation changes alone does not violate termination.\<close>
definition equational_step ::
  "'f arity \<Rightarrow> ('f,'v) rewriting_rules \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow>
    ('f, 'v) fo_term \<Rightarrow> ('f, 'v) fo_term \<Rightarrow> bool" where
  "equational_step A R FA FC s t \<longleftrightarrow>
    (\<exists>u v. equational_conversion A FA FC s u \<and>
      fo_step A R u v \<and> equational_conversion A FA FC v t)"
definition trs_equational_terminates ::
  "'f arity \<Rightarrow> ('f,'v) rewriting_rules \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow>
    bool" where
  "trs_equational_terminates A R FA FC \<longleftrightarrow>
    no_infinite_steps (equational_step A R FA FC)"
end
