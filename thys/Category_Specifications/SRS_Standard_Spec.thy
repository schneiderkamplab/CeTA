theory SRS_Standard_Spec
  imports SRS_Spec_Base
begin
text \<open>Termination excludes every infinite sequence of word replacements.\<close>
definition srs_standard_terminates where
  "srs_standard_terminates R \<longleftrightarrow> no_infinite_steps (string_step R)"
end
