theory LP_Terms_Spec
  imports TRS_Spec_Base Rewriting_Sequences_Spec
begin

text \<open>Program clauses and initial queries use the shared finite first-order
terms. Runtime trees are a separate domain so that unification without an occurs
check can represent cycles. A rational tree has only finitely many distinct
subtrees; the separate infinite-tree variant also permits non-rational trees. The variable type is a parameter; these definitions do not inspect variable
names or require a cardinality assumption.\<close>
codatatype ('f,'v) logic_tree = LVar 'v | LFun 'f "('f,'v) logic_tree list"

text \<open>Runtime trees respect the same arity function as finite terms.
The coinductive interpretation admits infinite trees while checking every node.\<close>
coinductive logic_tree_arity_correct ::
  "'f arity \<Rightarrow> ('f,'v) logic_tree \<Rightarrow> bool"
  for A where
  variable: "logic_tree_arity_correct A (LVar x)"
| application: "length ts = A f \<Longrightarrow>
    list_all (logic_tree_arity_correct A) ts \<Longrightarrow>
    logic_tree_arity_correct A (LFun f ts)"

fun logic_embed :: "('f,'v) fo_term \<Rightarrow> ('f,'v) logic_tree" where
  "logic_embed (SVar x) = LVar x"
| "logic_embed (SFun f ts) = LFun f (map logic_embed ts)"
primcorec logic_subst :: "('v \<Rightarrow> ('f,'v) logic_tree) \<Rightarrow> ('f,'v) logic_tree \<Rightarrow> ('f,'v) logic_tree" where
  "logic_subst s t = (case t of LVar x \<Rightarrow> s x
    | LFun f ts \<Rightarrow> LFun f (map (logic_subst s) ts))"
text \<open>Evaluation of a finite term abbreviates substitution after embedding;
it is not a second substitution operation.\<close>
abbreviation logic_eval ::
  "('v \<Rightarrow> ('f,'v) logic_tree) \<Rightarrow> ('f,'v) fo_term \<Rightarrow> ('f,'v) logic_tree" where
  "logic_eval s t \<equiv> logic_subst s (logic_embed t)"

text \<open>The relation logic_subtree u t means that u is a subtree of t, reached
by a finite path from the root (including the empty path).
Finiteness of the set of resulting trees permits cycles, not infinite growth
of distinct subtrees. Finiteness of a term instead means that it is the embedding
of an ordinary finite first-order term.\<close>
inductive logic_subtree :: "('f,'v) logic_tree \<Rightarrow> ('f,'v) logic_tree \<Rightarrow> bool" where
  root: "logic_subtree t t"
| child: "u \<in> set ts \<Longrightarrow> logic_subtree v u \<Longrightarrow> logic_subtree v (LFun f ts)"
definition logic_rational ::
  "('f, 'v) logic_tree \<Rightarrow> bool" where
  "logic_rational t \<longleftrightarrow> finite {u. logic_subtree u t}"
definition logic_finite ::
  "('f, 'v) logic_tree \<Rightarrow> bool" where
  "logic_finite t \<longleftrightarrow> (\<exists>u. t = logic_embed u)"
fun logic_ground :: "('f,'v) fo_term \<Rightarrow> bool" where
  "logic_ground (SVar x) = False"
| "logic_ground (SFun f ts) = list_all logic_ground ts"

text \<open>A substitution is simultaneous and must stay in the selected runtime
domain. The finite and rational instances below therefore differ at precisely
the occurs-check boundary.\<close>
definition logic_substitution_in ::
  "('t \<Rightarrow> bool) \<Rightarrow> ('v \<Rightarrow> 't) \<Rightarrow> bool" where
  "logic_substitution_in D s \<longleftrightarrow> (\<forall>x. D (s x))"

text \<open>Fresh clause variables are distinct and do not occur in the active
caller terms. Saved alternatives have separate bindings and are not part of
this variable set.\<close>
definition logic_variables :: "('f,'v) logic_tree \<Rightarrow> 'v set" where
  "logic_variables t = {x. logic_subtree (LVar x) t}"
definition logic_freshening ::
  "('v \<Rightarrow> 'v) \<Rightarrow> ('f,'v) logic_tree list \<Rightarrow>
    ('f,'v) fo_term list \<Rightarrow> bool" where
  "logic_freshening r active clause \<longleftrightarrow>
    (let X = \<Union>(logic_variables ` set active);
         Y = \<Union>((logic_variables \<circ> logic_embed) ` set clause)
     in inj_on r Y \<and> r ` Y \<inter> X = {})"

end
