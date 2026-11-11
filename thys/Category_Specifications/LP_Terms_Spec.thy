theory LP_Terms_Spec
  imports First_Order_Terms_Spec Rewriting_Sequences_Spec
begin

text \<open>Program clauses and initial queries use the shared finite first-order
terms. Runtime trees are a separate domain so that unification without an occurs
check can represent cycles. A rational tree has only finitely many distinct
subtrees; the separate infinite-tree variant also permits non-rational trees. Variables are
strings, an infinite supply.\<close>
codatatype 'f logic_tree = LVar string | LFun 'f "'f logic_tree list"

fun logic_embed :: "('f,string) fo_term \<Rightarrow> 'f logic_tree" where
  "logic_embed (SVar x) = LVar x"
| "logic_embed (SFun f ts) = LFun f (map logic_embed ts)"
primcorec logic_subst :: "(string \<Rightarrow> 'f logic_tree) \<Rightarrow> 'f logic_tree \<Rightarrow> 'f logic_tree" where
  "logic_subst s t = (case t of LVar x \<Rightarrow> s x
    | LFun f ts \<Rightarrow> LFun f (map (logic_subst s) ts))"
fun logic_eval :: "(string \<Rightarrow> 'f logic_tree) \<Rightarrow> ('f,string) fo_term \<Rightarrow> 'f logic_tree" where
  "logic_eval s (SVar x) = s x"
| "logic_eval s (SFun f ts) = LFun f (map (logic_eval s) ts)"

text \<open>The reflexive subtree relation visits any finite path from the root.
Finiteness of the set of resulting trees permits cycles, not infinite growth
of distinct subtrees. Finiteness of a term instead means that it is the embedding
of an ordinary finite first-order term.\<close>
inductive logic_subtree :: "'f logic_tree \<Rightarrow> 'f logic_tree \<Rightarrow> bool" where
  root: "logic_subtree t t"
| child: "u \<in> set ts \<Longrightarrow> logic_subtree u v \<Longrightarrow> logic_subtree (LFun f ts) v"
definition logic_rational where
  "logic_rational t \<longleftrightarrow> finite {u. logic_subtree t u}"
definition logic_finite where
  "logic_finite t \<longleftrightarrow> (\<exists>u. t = logic_embed u)"
fun logic_ground :: "('f,string) fo_term \<Rightarrow> bool" where
  "logic_ground (SVar x) = False"
| "logic_ground (SFun f ts) = list_all logic_ground ts"

text \<open>A substitution is simultaneous and must stay in the selected runtime
domain. The finite and rational instances below therefore differ at precisely
the occurs-check boundary.\<close>
definition logic_substitution where
  "logic_substitution D s \<longleftrightarrow> (\<forall>x. D (s x))"

end
