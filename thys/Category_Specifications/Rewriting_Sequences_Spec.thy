theory Rewriting_Sequences_Spec
  imports Main
begin

text \<open>A finite sequence can contain zero steps. The second clause appends
one step to an already finite sequence.\<close>
inductive finite_steps :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for step where
  zero: "finite_steps step s s"
| append: "finite_steps step s t \<Longrightarrow> step t u \<Longrightarrow> finite_steps step s u"

text \<open>Termination excludes every sequence indexed by the natural numbers.\<close>
definition no_infinite_steps where
  "no_infinite_steps step \<longleftrightarrow> \<not> (\<exists>ts. \<forall>i. step (ts i) (ts (Suc i)))"
end
