theory TRS_Standard_Spec
  imports TRS_Spec_Base Rewriting_Sequences_Spec
begin

text \<open>Termination means that no infinite sequence of rewrite steps exists.
For the ranked TRS Standard category, use this predicate with trs_problem.
The sequence ranges over arbitrary terms, not just ground terms.\<close>
definition trs_standard_terminates ::
  "'f ranked_signature \<Rightarrow> (('f,'v) fo_term \<times> ('f,'v) fo_term) set \<Rightarrow> bool"
where
  "trs_standard_terminates A R \<longleftrightarrow>
    no_infinite_steps (fo_step A R)"
end
