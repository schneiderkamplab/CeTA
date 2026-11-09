theory TRS_Conditional_Operational_Spec
  imports TRS_Conditional_Ordinary_Spec
begin
text \<open>Operational termination excludes infinite branches of ordered proof
attempts. This includes evaluation of conditions that never return. Quantification
is over all goals on arbitrary terms, not only ground terms or successful goals.\<close>
definition trs_conditional_operationally_terminates where
  "trs_conditional_operationally_terminates A R \<longleftrightarrow>
    no_infinite_steps (conditional_evaluation_step A R)"
end
