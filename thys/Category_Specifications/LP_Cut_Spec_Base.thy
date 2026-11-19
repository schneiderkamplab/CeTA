theory LP_Cut_Spec_Base
  imports LP_Spec_Base
begin

text \<open>Ordered logic programs with cut retain a stack of alternatives and
invocation barriers. Literal cuts in a clause acquire the barrier of that
invocation. A successful goal resumes saved alternatives: termination means
exhausting the computation, not merely producing its first answer.
The constructors distinguish control from user predicate names.\<close>
datatype 'f logic_symbol = LogicUser 'f | LogicBang | LogicComma | LogicEquals
  | LogicTrue | LogicFail | LogicCall
datatype ('p,'t) logic_goal = LogicAtom "('p,'t) logic_atom" | LogicCut nat | LogicSuccess | LogicFailure
  | LogicMeta 't | LogicUnify 't 't
datatype ('p,'t) logic_choice = LogicGoals "('p,'t) logic_goal list"
  | LogicClause "('p,'t) logic_goal list" nat nat | LogicBarrier nat

fun logic_goal_map ::
  "('a \<Rightarrow> 'b) \<Rightarrow> ('p,'a) logic_goal \<Rightarrow> ('p,'b) logic_goal" where
  "logic_goal_map f (LogicAtom a) = LogicAtom (logic_atom_map f a)"
| "logic_goal_map f (LogicCut m) = LogicCut m"
| "logic_goal_map f LogicSuccess = LogicSuccess"
| "logic_goal_map f LogicFailure = LogicFailure"
| "logic_goal_map f (LogicMeta a) = LogicMeta (f a)"
| "logic_goal_map f (LogicUnify a b) = LogicUnify (f a) (f b)"
fun logic_goal_terms ::
  "('p,'a) logic_goal \<Rightarrow> 'a list" where
  "logic_goal_terms (LogicAtom a) = logic_arguments a"
| "logic_goal_terms (LogicMeta a) = [a]"
| "logic_goal_terms (LogicUnify a b) = [a,b]"
| "logic_goal_terms _ = []"
fun logic_bind_cut ::
  "nat \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('p,'a) logic_goal \<Rightarrow> ('p,'b) logic_goal" where
  "logic_bind_cut m f (LogicCut n) = LogicCut m"
| "logic_bind_cut m f g = logic_goal_map f g"
fun logic_goal_marks ::
  "('p,'a) logic_goal \<Rightarrow> nat set" where
  "logic_goal_marks (LogicCut m) = {m}"
| "logic_goal_marks _ = {}"
fun logic_choice_marks ::
  "('p,'a) logic_choice \<Rightarrow> nat set" where
  "logic_choice_marks (LogicGoals gs) = \<Union>(logic_goal_marks ` set gs)"
| "logic_choice_marks (LogicClause gs c m) = insert m (\<Union>(logic_goal_marks ` set gs))"
| "logic_choice_marks (LogicBarrier m) = {m}"
definition logic_fresh_mark ::
  "nat \<Rightarrow> ('p,'a) logic_choice list \<Rightarrow> bool" where
  "logic_fresh_mark m es \<longleftrightarrow> m \<notin> \<Union>(logic_choice_marks ` set es)"

text \<open>A cut discards alternatives up to its own barrier, retaining that
barrier and the caller's alternatives. Resolution never substitutes into saved
alternatives: their variable bindings are restored when backtracking.\<close>
fun logic_prune ::
  "nat \<Rightarrow> ('p,'a) logic_choice list \<Rightarrow> ('p,'a) logic_choice list" where
  "logic_prune m [] = []"
| "logic_prune m (e#es) = (case e of LogicBarrier n \<Rightarrow>
    if m=n then e#es else logic_prune m es | _ \<Rightarrow> logic_prune m es)"
fun logic_admin ::
  "('p,'a) logic_choice list \<Rightarrow> ('p,'a) logic_choice list option" where
  "logic_admin [] = None"
| "logic_admin (LogicBarrier m#es) = Some es"
| "logic_admin (LogicClause gs c m#es) = None"
| "logic_admin (LogicGoals []#es) = Some es"
| "logic_admin (LogicGoals (g#gs)#es) = (case g of
    LogicSuccess \<Rightarrow> Some (LogicGoals gs#es)
  | LogicFailure \<Rightarrow> Some es
  | LogicCut m \<Rightarrow> Some (LogicGoals gs#logic_prune m es)
  | _ \<Rightarrow> None)"

text \<open>User symbols use the same global arities as pure LP. Control symbols
have the arities of their syntax, including unary call.\<close>
fun logic_symbol_arity :: "'f arity \<Rightarrow> 'f logic_symbol arity" where
  "logic_symbol_arity A (LogicUser f) = A f"
| "logic_symbol_arity A LogicBang = 0"
| "logic_symbol_arity A LogicTrue = 0"
| "logic_symbol_arity A LogicFail = 0"
| "logic_symbol_arity A LogicComma = 2"
| "logic_symbol_arity A LogicEquals = 2"
| "logic_symbol_arity A LogicCall = 1"
type_synonym ('f,'v) logic_cut_program =
  "(('f,('f logic_symbol,'v) fo_term) logic_atom \<times>
    ('f,('f logic_symbol,'v) fo_term) logic_goal list) list"
definition logic_slice ::
  "(('f,'t) logic_atom \<times> 'body) list \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> nat list" where
  "logic_slice P f n = filter (\<lambda>c. logic_predicate (fst (P!c)) = f \<and>
    length (logic_arguments (fst (P!c))) = n) [0..<length P]"

text \<open>Meta-calls receive their own cut scope. Decode a whole conjunction
before executing it; variable leaves remain opaque meta-calls. An unbound
meta-call has no successor.\<close>
inductive logic_lower ::
  "nat \<Rightarrow> ('f logic_symbol,'v) logic_tree \<Rightarrow>
    ('f,('f logic_symbol,'v) logic_tree) logic_goal list \<Rightarrow> bool"
  for m where
  variable: "logic_lower m (LVar x) [LogicMeta (LVar x)]"
| atom: "logic_lower m (LFun (LogicUser f) ts) [LogicAtom (LAtom f ts)]"
| cut: "logic_lower m (LFun LogicBang []) [LogicCut m]"
| conjunction: "logic_lower m a gs \<Longrightarrow> logic_lower m b hs \<Longrightarrow>
    logic_lower m (LFun LogicComma [a,b]) (gs@hs)"
| unify: "logic_lower m (LFun LogicEquals [a,b]) [LogicUnify a b]"
| success: "logic_lower m (LFun LogicTrue []) [LogicSuccess]"
| failure: "logic_lower m (LFun LogicFail []) [LogicFailure]"
| call: "logic_lower m (LFun LogicCall [a]) [LogicMeta a]"

text \<open>A cyclic conjunction may require infinitely much decoding. The left
conjunct is decoded first; the right is visited only after a finite left decoding.\<close>
coinductive logic_lower_diverges :: "('f logic_symbol,'v) logic_tree \<Rightarrow> bool" where
  left: "logic_lower_diverges a \<Longrightarrow> logic_lower_diverges (LFun LogicComma [a,b])"
| right: "logic_lower 0 a gs \<Longrightarrow> logic_lower_diverges b \<Longrightarrow>
    logic_lower_diverges (LFun LogicComma [a,b])"

text \<open>Clause order determines the saved alternatives. Resolution freshens
against all active goals, then applies one domain-correct MGU to the renamed
body and continuation. Saved alternatives retain their old bindings. Failure
means that no unifier exists in the same signature and term domain.\<close>
inductive logic_cut_step ::
  "'f arity \<Rightarrow> (('f logic_symbol,'v) logic_tree \<Rightarrow> bool) \<Rightarrow> ('f,'v) logic_cut_program \<Rightarrow>
    ('f,('f logic_symbol,'v) logic_tree) logic_choice list \<Rightarrow>
    ('f,('f logic_symbol,'v) logic_tree) logic_choice list \<Rightarrow> bool" for A D P where
  admin: "logic_admin s = Some t \<Longrightarrow> logic_cut_step A D P s t"
| case_call: "logic_fresh_mark m (LogicGoals (LogicAtom (LAtom f ts)#gs)#es) \<Longrightarrow>
    logic_cut_step A D P (LogicGoals (LogicAtom (LAtom f ts)#gs)#es)
      (map (\<lambda>c. LogicClause (LogicAtom (LAtom f ts)#gs) c m)
        (logic_slice P f (length ts)) @ LogicBarrier m#es)"
| resolve: "c<length P \<Longrightarrow>
    logic_freshening r (logic_arguments a @ concat (map logic_goal_terms gs))
      (logic_arguments (fst (P!c)) @ concat (map logic_goal_terms (snd (P!c)))) \<Longrightarrow>
    logic_mgu (\<lambda>t. D t \<and> logic_tree_arity_correct (logic_symbol_arity A) t)
      a (logic_atom_map (logic_eval (LVar \<circ> r)) (fst (P!c))) s \<Longrightarrow>
    logic_cut_step A D P (LogicClause (LogicAtom a#gs) c m#es)
      (LogicGoals (map (logic_bind_cut m (logic_subst s \<circ> logic_eval (LVar \<circ> r))) (snd (P!c)) @
        map (logic_goal_map (logic_subst s)) gs)#es)"
| backtrack: "c<length P \<Longrightarrow>
    logic_freshening r (logic_arguments a @ concat (map logic_goal_terms gs))
      (logic_arguments (fst (P!c)) @ concat (map logic_goal_terms (snd (P!c)))) \<Longrightarrow>
    \<not> (\<exists>s. logic_substitution_in (\<lambda>t. D t \<and> logic_tree_arity_correct (logic_symbol_arity A) t) s \<and>
      logic_atom_map (logic_subst s) a =
        logic_atom_map (logic_subst s \<circ> logic_eval (LVar \<circ> r)) (fst (P!c))) \<Longrightarrow>
    logic_cut_step A D P (LogicClause (LogicAtom a#gs) c m#es) es"
| unify: "logic_mgu (\<lambda>t. D t \<and> logic_tree_arity_correct (logic_symbol_arity A) t)
      (LAtom () [a]) (LAtom () [b]) s \<Longrightarrow>
    logic_cut_step A D P (LogicGoals (LogicUnify a b#gs)#es)
      (LogicGoals (map (logic_goal_map (logic_subst s)) gs)#es)"
| unify_fail: "\<not> (\<exists>s. logic_substitution_in (\<lambda>t. D t \<and> logic_tree_arity_correct (logic_symbol_arity A) t) s \<and>
      logic_subst s a = logic_subst s b) \<Longrightarrow>
    logic_cut_step A D P (LogicGoals (LogicUnify a b#gs)#es) es"
| meta: "logic_fresh_mark m (LogicGoals (LogicMeta (LFun f ts)#gs)#es) \<Longrightarrow>
    logic_lower m (LFun f ts) body \<Longrightarrow>
    logic_cut_step A D P (LogicGoals (LogicMeta (LFun f ts)#gs)#es)
      (LogicGoals (body@gs)#LogicBarrier m#es)"
| meta_diverges: "logic_lower_diverges a \<Longrightarrow>
    logic_cut_step A D P (LogicGoals (LogicMeta a#gs)#es) (LogicGoals (LogicMeta a#gs)#es)"

fun logic_goal_correct :: "'f arity \<Rightarrow> ('f,('f logic_symbol,'v) fo_term) logic_goal \<Rightarrow> bool" where
  "logic_goal_correct A (LogicAtom a) = logic_atom_correct A (arity_correct (logic_symbol_arity A)) a"
| "logic_goal_correct A g = list_all (arity_correct (logic_symbol_arity A)) (logic_goal_terms g)"
text \<open>Valid programs have arity-correct heads and bodies; the query mode
has exactly the selected predicate's arity. This is separate from termination.\<close>
definition logic_cut_problem ::
  "'f arity \<Rightarrow> ('f,'v) logic_cut_program \<Rightarrow> 'f \<Rightarrow> bool list \<Rightarrow> bool" where
  "logic_cut_problem A P p modes \<longleftrightarrow> length modes = A p \<and>
    (\<forall>(h,bs)\<in>set P. logic_atom_correct A (arity_correct (logic_symbol_arity A)) h \<and>
      list_all (logic_goal_correct A) bs)"
definition logic_cut_terminates_in ::
  "'f arity \<Rightarrow> (('f logic_symbol,'v) logic_tree \<Rightarrow> bool) \<Rightarrow> ('f,'v) logic_cut_program
    \<Rightarrow> 'f \<Rightarrow> bool list \<Rightarrow> bool" where
  "logic_cut_terminates_in A D P p modes \<longleftrightarrow>
    \<not> (\<exists>ts s.
      logic_query (logic_symbol_arity A) (LogicUser p) modes (LAtom (LogicUser p) ts) \<and>
      s 0 = [LogicGoals [LogicAtom (LAtom p (map logic_embed ts))]] \<and>
      (\<forall>n. logic_cut_step A D P (s n) (s (Suc n))))"

end
