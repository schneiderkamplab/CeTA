theory ITS_Spec
  imports Rewriting_Sequences_Spec
begin

text \<open>A store assigns mathematical integers, without overflow, to variables.
A transition has a source and target location and a relation on the pre-store,
post-store and local store. The local store is existentially chosen afresh for
each step. Guards are mathematical predicates: arithmetic syntax and its parsing
are separate representations of these predicates. Updates are simultaneous;
a variable left unconstrained by the relation is nondeterministic.\<close>
type_synonym 'v integer_store = "'v \<Rightarrow> int"
type_synonym ('l,'v) integer_transition =
  "'l \<times> 'l \<times> ('v integer_store \<Rightarrow> 'v integer_store \<Rightarrow> 'v integer_store \<Rightarrow> bool)"

text \<open>The relational system specifies entry locations, finitely many transitions,
and a permitted-store predicate at every location. With no location assertion,
this predicate is constantly true. Boolean arguments can occupy separate store slots
constrained to 0 and 1. The variable universe itself need not be finite.
The category requires exactly one entry location; the underlying execution
definitions also make sense for multiple entries.\<close>
record ('l,'v) integer_system =
  its_entries :: "'l set"
  its_rules :: "('l,'v) integer_transition set"
  its_allowed :: "'l \<Rightarrow> 'v integer_store \<Rightarrow> bool"

definition its_problem where
  "its_problem P \<longleftrightarrow> (\<exists>l. its_entries P = {l}) \<and> finite (its_rules P)"

text \<open>A state is a location and a store. Initial stores are arbitrary
permitted stores at entry locations; termination is not required at unreachable
states. Both endpoints of a step must satisfy their location assertions.\<close>
definition its_initial where
  "its_initial P s \<longleftrightarrow> fst s \<in> its_entries P \<and> its_allowed P (fst s) (snd s)"
definition its_step where
  "its_step P s t \<longleftrightarrow>
    its_allowed P (fst s) (snd s) \<and> its_allowed P (fst t) (snd t) \<and>
    (\<exists>g z. (fst s, fst t, g) \<in> its_rules P \<and> g (snd s) (snd t) z)"

text \<open>Termination excludes an infinite execution from any initial state.
Nontermination is its negation, hence requires an initial state and one infinite
execution. The final property does not assert that every state is reachable.\<close>
definition its_terminates where
  "its_terminates P \<longleftrightarrow>
    \<not> (\<exists>s. its_initial P (s 0) \<and> (\<forall>n. its_step P (s n) (s (Suc n))))"

end
