theory LP_Spec_Base
  imports LP_Terms_Spec
begin

text \<open>Predicate applications have their own constructor. Clause bodies are
ordered; a program is a finite list of head/body pairs and may repeat clauses.\<close>
datatype ('p,'t) logic_atom = LAtom (logic_predicate: 'p) (logic_arguments: "'t list")
type_synonym ('f,'v) logic_clause =
  "('f,('f,'v) fo_term) logic_atom \<times> ('f,('f,'v) fo_term) logic_atom list"
fun logic_atom_map ::
  "('s \<Rightarrow> 't) \<Rightarrow> ('p,'s) logic_atom \<Rightarrow> ('p,'t) logic_atom" where
  "logic_atom_map g (LAtom p ts) = LAtom p (map g ts)"

text \<open>The arity function fixes each predicate's argument count. A separate
term predicate allows the same definition to check finite and runtime atoms.\<close>
fun logic_atom_correct :: "'p arity \<Rightarrow> ('t \<Rightarrow> bool) \<Rightarrow> ('p,'t) logic_atom \<Rightarrow> bool" where
  "logic_atom_correct A T (LAtom p ts) \<longleftrightarrow> length ts = A p \<and> list_all T ts"
definition logic_problem ::
  "'f arity \<Rightarrow> ('f,'v) logic_clause list \<Rightarrow> 'f \<Rightarrow> bool list \<Rightarrow> bool" where
  "logic_problem A P p modes \<longleftrightarrow> length modes = A p \<and>
    (\<forall>(h,bs)\<in>set P. list_all (logic_atom_correct A (arity_correct A)) (h#bs))"

text \<open>A most-general unifier is one substitution that unifies the atoms.
Every other domain-correct unifier factors through it on every variable.\<close>
definition logic_mgu ::
  "(('f,'v) logic_tree \<Rightarrow> bool) \<Rightarrow>
    ('p,('f,'v) logic_tree) logic_atom \<Rightarrow>
    ('p,('f,'v) logic_tree) logic_atom \<Rightarrow>
    ('v \<Rightarrow> ('f,'v) logic_tree) \<Rightarrow> bool" where
  "logic_mgu D a b s \<longleftrightarrow>
    logic_substitution_in D s \<and>
    logic_atom_map (logic_subst s) a = logic_atom_map (logic_subst s) b \<and>
    (\<forall>u. logic_substitution_in D u \<and>
      logic_atom_map (logic_subst u) a = logic_atom_map (logic_subst u) b
      \<longrightarrow> (\<exists>v. logic_substitution_in D v \<and>
        (\<forall>x. u x = logic_subst v (s x))))"

text \<open>Leftmost resolution first renames the selected clause apart from
all current goals, then embeds it and computes one MGU. That substitution acts
on both the renamed body and the remaining goals. Any clause may be selected.\<close>
inductive logic_step ::
  "'f arity \<Rightarrow> (('f,'v) logic_tree \<Rightarrow> bool) \<Rightarrow> ('f,'v) logic_clause list \<Rightarrow>
    ('f,('f,'v) logic_tree) logic_atom list \<Rightarrow> ('f,('f,'v) logic_tree) logic_atom list \<Rightarrow> bool"
  for A D P where
  resolve: "(h,bs) \<in> set P \<Longrightarrow>
    logic_freshening r (concat (map logic_arguments (a#gs)))
      (concat (map logic_arguments (h#bs))) \<Longrightarrow>
    logic_mgu (\<lambda>t. D t \<and> logic_tree_arity_correct A t)
      a (logic_atom_map (logic_eval (LVar \<circ> r)) h) s \<Longrightarrow>
    logic_step A D P (a#gs)
      (map (logic_atom_map (logic_subst s))
        (map (logic_atom_map (logic_eval (LVar \<circ> r))) bs @ gs))"

text \<open>Initial arguments are finite terms. Ground modes require no variables;
arbitrary modes permit sharing and are not limited to fresh variables.\<close>
definition logic_query ::
  "'f arity \<Rightarrow> 'f \<Rightarrow> bool list \<Rightarrow> ('f,('f,'v) fo_term) logic_atom \<Rightarrow> bool" where
  "logic_query A p modes a \<longleftrightarrow>
    logic_predicate a = p \<and> length modes = A p \<and>
    logic_atom_correct A (arity_correct A) a \<and>
    list_all (\<lambda>(t,b). b \<longrightarrow> logic_ground t) (zip (logic_arguments a) modes)"
text \<open>For a valid logic_problem, termination means that no infinite
leftmost derivation starts from any query in the declared mode class.\<close>
definition logic_terminates_in ::
  "'f arity \<Rightarrow> (('f,'v) logic_tree \<Rightarrow> bool) \<Rightarrow> ('f,'v) logic_clause list \<Rightarrow> 'f
    \<Rightarrow> bool list \<Rightarrow> bool" where
  "logic_terminates_in A D P p modes \<longleftrightarrow>
    \<not> (\<exists>a s. logic_query A p modes a \<and>
      s 0 = [logic_atom_map logic_embed a] \<and>
      (\<forall>n. logic_step A D P (s n) (s (Suc n))))"

end
