theory SRS_Cycle_Spec
  imports SRS_Spec_Base
begin
text \<open>Words represent cycles up to rotation. A cycle step chooses a
rotation, performs one genuine replacement, and may rotate the result.
Rotation alone does not count as a step, even for the empty word.\<close>
definition cycle_string_step ::
  "'a string_rewriting_rules \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "cycle_string_step R s t \<longleftrightarrow>
    (\<exists>a b c d. s = a @ b \<and> string_step R (b @ a) (c @ d) \<and> t = d @ c)"
definition srs_cycle_terminates ::
  "'a string_rewriting_rules \<Rightarrow> bool" where
  "srs_cycle_terminates R \<longleftrightarrow> no_infinite_steps (cycle_string_step R)"
end
