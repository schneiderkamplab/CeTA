theory SRS_Relative_Spec
  imports SRS_Spec_Base
begin
text \<open>A relative problem has a finite set R of strict word rules and a
finite set S of weak word rules.\<close>
definition relative_string_problem ::
  "'a string_rewriting_rules \<Rightarrow> 'a string_rewriting_rules \<Rightarrow> bool" where
  "relative_string_problem R S \<longleftrightarrow> string_problem R \<and> string_problem S"

text \<open>A relative block has one strict replacement between finite sequences
of weak replacements. Infinite weak-only rewriting is permitted.\<close>
definition relative_string_step ::
  "'a string_rewriting_rules \<Rightarrow> 'a string_rewriting_rules \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "relative_string_step R S s t \<longleftrightarrow>
    (\<exists>u v. finite_steps (string_step S) s u \<and>
      string_step R u v \<and> finite_steps (string_step S) v t)"
definition srs_relative_terminates ::
  "'a string_rewriting_rules \<Rightarrow> 'a string_rewriting_rules \<Rightarrow> bool" where
  "srs_relative_terminates R S \<longleftrightarrow> no_infinite_steps (relative_string_step R S)"
end
