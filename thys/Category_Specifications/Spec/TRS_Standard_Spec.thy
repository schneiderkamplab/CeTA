theory TRS_Standard_Spec
  imports TRS_Spec_Base
begin

text \<open>Termination means that no infinite sequence of rewrite steps exists.
For the ranked TRS Standard category, use this predicate with standard_problem.
The sequence ranges over arbitrary terms, not just ground terms.\<close>
definition trs_standard_terminates ::
  "'f ranked_signature \<Rightarrow> (('f,'v) standard_term \<times> ('f,'v) standard_term) set \<Rightarrow> bool"
where
  "trs_standard_terminates A R \<longleftrightarrow>
    \<not> (\<exists>ts :: nat \<Rightarrow> ('f, 'v) standard_term. \<forall>i. standard_step A R (ts i) (ts (Suc i)))"

lemma trs_standard_nontermination_iff:
  "\<not> trs_standard_terminates A R \<longleftrightarrow>
    (\<exists>ts. \<forall>i. standard_step A R (ts i) (ts (Suc i)))"
  by (simp add: trs_standard_terminates_def)

end
