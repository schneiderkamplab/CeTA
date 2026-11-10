theory LP_Spec_Base
  imports LP_Terms_Spec
begin

text \<open>An atom separates its predicate from its argument terms. Clauses are
finite head/body pairs; a program is a finite list of clauses. Bodies are ordered.
Predicates are identified by name and arity. Repeated clauses are permitted.\<close>
type_synonym ('f,'t) logic_atom = "'f \<times> 't list"
type_synonym 'f logic_clause =
  "('f,('f,string) fo_term) logic_atom \<times> ('f,('f,string) fo_term) logic_atom list"
definition logic_atom_map where
  "logic_atom_map f a = (fst a, map f (snd a))"

text \<open>Two substitutions use independent variable namespaces for the caller
and the clause, expressing fresh clause variables without selecting particular
fresh names. Most-generality requires every competing solution to factor through
the result, including the remaining caller goals and the clause body. This
prevents arbitrary specialization of variables outside the selected equation.\<close>
definition logic_mgu where
  "logic_mgu D a gs h bs s r \<longleftrightarrow>
    logic_substitution D s \<and> logic_substitution D r \<and>
    logic_atom_map (logic_subst s) a = logic_atom_map (logic_eval r) h \<and>
    (\<forall>t u. logic_substitution D t \<longrightarrow> logic_substitution D u \<longrightarrow>
      logic_atom_map (logic_subst t) a = logic_atom_map (logic_eval u) h \<longrightarrow>
      (\<exists>d. logic_substitution D d \<and>
        logic_atom_map (logic_subst d \<circ> logic_subst s) a = logic_atom_map (logic_subst t) a \<and>
        map (logic_atom_map (logic_subst d \<circ> logic_subst s)) gs = map (logic_atom_map (logic_subst t)) gs \<and>
        map (logic_atom_map (logic_subst d \<circ> logic_eval r)) bs = map (logic_atom_map (logic_eval u)) bs))"

text \<open>Leftmost resolution replaces the first atom by the selected clause's
body and propagates the same substitution through the remaining goals. Any
matching clause may be chosen: the property concerns all derivations, not just
the first answer. An empty goal has no successor.\<close>
inductive logic_step ::
  "('f logic_tree \<Rightarrow> bool) \<Rightarrow> 'f logic_clause list \<Rightarrow>
    ('f,'f logic_tree) logic_atom list \<Rightarrow> ('f,'f logic_tree) logic_atom list \<Rightarrow> bool"
  for D P where
  resolve: "(h,bs) \<in> set P \<Longrightarrow> logic_mgu D a gs h bs s r \<Longrightarrow>
    logic_step D P (a#gs)
      (map (logic_atom_map (logic_eval r)) bs @ map (logic_atom_map (logic_subst s)) gs)"

text \<open>Each query mode specifies ground or arbitrary arguments. An arbitrary
argument need not be a fresh variable: it may be any finite term, and arguments
may share variables. Initial queries are finite in both runtime semantics.\<close>
definition logic_query where
  "logic_query p modes a \<longleftrightarrow> fst a = p \<and> length (snd a) = length modes \<and>
    list_all (\<lambda>(t,b). b \<longrightarrow> logic_ground t) (zip (snd a) modes)"
definition logic_terminates_in where
  "logic_terminates_in D P p modes \<longleftrightarrow>
    \<not> (\<exists>a s. logic_query p modes a \<and>
      s 0 = [logic_atom_map logic_embed a] \<and>
      (\<forall>n. logic_step D P (s n) (s (Suc n))))"

end
