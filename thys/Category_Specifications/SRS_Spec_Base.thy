theory SRS_Spec_Base
  imports Rewriting_Sequences_Spec
begin
text \<open>Words are finite lists over an alphabet. A string system is a finite
set of pairs of words. Empty words, including empty left sides, are allowed.\<close>
type_synonym 'a string_rewriting_rules = "('a list \<times> 'a list) set"

definition string_problem :: "'a string_rewriting_rules \<Rightarrow> bool" where
  "string_problem R \<longleftrightarrow> finite R"
text \<open>A step replaces one contiguous occurrence of a left side by its
right side, preserving the prefix and suffix.\<close>
definition string_step ::
  "'a string_rewriting_rules \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "string_step R s t \<longleftrightarrow>
    (\<exists>l r u v. (l,r) \<in> R \<and> s = u @ l @ v \<and> t = u @ r @ v)"
end
