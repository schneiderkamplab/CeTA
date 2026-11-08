theory SRS_Relative_Spec
  imports SRS_Spec_Base
begin
text \<open>A relative block has one strict replacement between finite sequences
of weak replacements. Infinite weak-only rewriting is permitted. Both rule
collections separately satisfy string_problem.\<close>
definition relative_string_step where
  "relative_string_step R S s t \<longleftrightarrow>
    (\<exists>u v. finite_steps (string_step S) s u \<and>
      string_step R u v \<and> finite_steps (string_step S) v t)"
definition srs_relative_terminates where
  "srs_relative_terminates R S \<longleftrightarrow> no_infinite_steps (relative_string_step R S)"
lemma srs_relative_nontermination_iff:
  "\<not> srs_relative_terminates R S \<longleftrightarrow>
    (\<exists>ws. \<forall>i. relative_string_step R S (ws i) (ws (Suc i)))"
  by (simp add: srs_relative_terminates_def infinite_steps_iff)
end
