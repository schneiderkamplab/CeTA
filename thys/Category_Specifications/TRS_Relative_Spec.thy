theory TRS_Relative_Spec
  imports TRS_Spec_Base Rewriting_Sequences_Spec
begin

text \<open>Strict and weak rules are both finite and signature-correct, with
infinitely many variables. No variable restriction is silently imposed.\<close>
definition relative_problem where
  "relative_problem A R S \<longleftrightarrow> trs_problem A R \<and> trs_problem A S"

text \<open>One relative step contains exactly one strict step, preceded and
followed by any finite number of weak steps. An infinite sequence therefore
uses infinitely many strict steps. An infinite weak-only sequence is allowed.\<close>
definition relative_step where
  "relative_step A R S s t \<longleftrightarrow>
    (\<exists>u v. finite_steps (fo_step A S) s u \<and>
      fo_step A R u v \<and> finite_steps (fo_step A S) v t)"
definition trs_relative_terminates where
  "trs_relative_terminates A R S \<longleftrightarrow> no_infinite_steps (relative_step A R S)"
end
