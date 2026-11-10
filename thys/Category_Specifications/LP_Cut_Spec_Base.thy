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
datatype 't logic_goal = LogicAtom 't | LogicCut nat | LogicSuccess | LogicFailure
  | LogicMeta 't | LogicUnify 't 't
datatype 't logic_choice = LogicGoals "'t logic_goal list"
  | LogicClause "'t logic_goal list" nat nat | LogicBarrier nat

fun logic_goal_map where
  "logic_goal_map f (LogicAtom a) = LogicAtom (f a)"
| "logic_goal_map f (LogicCut m) = LogicCut m"
| "logic_goal_map f LogicSuccess = LogicSuccess"
| "logic_goal_map f LogicFailure = LogicFailure"
| "logic_goal_map f (LogicMeta a) = LogicMeta (f a)"
| "logic_goal_map f (LogicUnify a b) = LogicUnify (f a) (f b)"
fun logic_goal_terms where
  "logic_goal_terms (LogicAtom a) = [a]"
| "logic_goal_terms (LogicMeta a) = [a]"
| "logic_goal_terms (LogicUnify a b) = [a,b]"
| "logic_goal_terms _ = []"
fun logic_bind_cut where
  "logic_bind_cut m f (LogicCut n) = LogicCut m"
| "logic_bind_cut m f g = logic_goal_map f g"
fun logic_goal_marks where
  "logic_goal_marks (LogicCut m) = {m}"
| "logic_goal_marks _ = {}"
fun logic_choice_marks where
  "logic_choice_marks (LogicGoals gs) = \<Union>(logic_goal_marks ` set gs)"
| "logic_choice_marks (LogicClause gs c m) = insert m (\<Union>(logic_goal_marks ` set gs))"
| "logic_choice_marks (LogicBarrier m) = {m}"
definition logic_fresh_mark where
  "logic_fresh_mark m es \<longleftrightarrow> m \<notin> \<Union>(logic_choice_marks ` set es)"

text \<open>A cut discards alternatives up to its own barrier, retaining that
barrier and the caller's alternatives. Resolution never substitutes into saved
alternatives: their variable bindings are restored when backtracking.\<close>
fun logic_prune where
  "logic_prune m [] = []"
| "logic_prune m (e#es) = (case e of LogicBarrier n \<Rightarrow>
    if m=n then e#es else logic_prune m es | _ \<Rightarrow> logic_prune m es)"
fun logic_admin where
  "logic_admin [] = None"
| "logic_admin (LogicBarrier m#es) = Some es"
| "logic_admin (LogicClause gs c m#es) = None"
| "logic_admin (LogicGoals []#es) = Some es"
| "logic_admin (LogicGoals (g#gs)#es) = (case g of
    LogicSuccess \<Rightarrow> Some (LogicGoals gs#es)
  | LogicFailure \<Rightarrow> Some es
  | LogicCut m \<Rightarrow> Some (LogicGoals gs#logic_prune m es)
  | _ \<Rightarrow> None)"

type_synonym 'f logic_cut_program =
  "(('f logic_symbol,string) fo_term \<times> ('f logic_symbol,string) fo_term logic_goal list) list"
definition logic_slice where
  "logic_slice P f n = filter (\<lambda>c. \<exists>ts. fst (P!c) = SFun (LogicUser f) ts \<and>
    length ts=n) [0..<length P]"

text \<open>Meta-calls receive their own cut scope. Decode the whole conjunction
before execution, leaving variable leaves as opaque meta-calls: later binding
a leaf to a cut must not give it the enclosing conjunction's scope. An unbound
meta-call or malformed callable is a finite error, with no successor.\<close>
inductive logic_lower ::
  "nat \<Rightarrow> 'f logic_symbol logic_tree \<Rightarrow> 'f logic_symbol logic_tree logic_goal list \<Rightarrow> bool"
  for m where
  variable: "logic_lower m (LVar x) [LogicMeta (LVar x)]"
| atom: "logic_lower m (LFun (LogicUser f) ts) [LogicAtom (LFun (LogicUser f) ts)]"
| cut: "logic_lower m (LFun LogicBang []) [LogicCut m]"
| conjunction: "logic_lower m a gs \<Longrightarrow> logic_lower m b hs \<Longrightarrow>
    logic_lower m (LFun LogicComma [a,b]) (gs@hs)"
| unify: "logic_lower m (LFun LogicEquals [a,b]) [LogicUnify a b]"
| success: "logic_lower m (LFun LogicTrue []) [LogicSuccess]"
| failure: "logic_lower m (LFun LogicFail []) [LogicFailure]"
| call: "logic_lower m (LFun LogicCall [a]) [LogicMeta a]"

text \<open>A cyclic conjunction can require infinitely much decoding. This
case is distinct from a malformed callable. Decoding visits the left conjunct
first; it visits the right only after the left has a finite decoding.\<close>
coinductive logic_lower_diverges :: "'f logic_symbol logic_tree \<Rightarrow> bool" where
  left: "logic_lower_diverges a \<Longrightarrow> logic_lower_diverges (LFun LogicComma [a,b])"
| right: "logic_lower 0 a gs \<Longrightarrow> logic_lower_diverges b \<Longrightarrow>
    logic_lower_diverges (LFun LogicComma [a,b])"

definition logic_cut_mgu where
  "logic_cut_mgu D a gs h bs s r \<longleftrightarrow>
    logic_mgu D ((),[a]) (map (\<lambda>t. ((),[t])) (concat (map logic_goal_terms gs)))
      ((),[h]) (map (\<lambda>t. ((),[t])) (concat (map logic_goal_terms bs))) s r"
definition logic_unify_mgu where
  "logic_unify_mgu D a b gs s \<longleftrightarrow>
    logic_substitution D s \<and> logic_subst s a = logic_subst s b \<and>
    (\<forall>t. logic_substitution D t \<longrightarrow> logic_subst t a = logic_subst t b \<longrightarrow>
      (\<exists>d. logic_substitution D d \<and> logic_subst d (logic_subst s a) = logic_subst t a \<and>
        map (logic_goal_map (logic_subst d \<circ> logic_subst s)) gs =
          map (logic_goal_map (logic_subst t)) gs))"

text \<open>Case analysis preserves source clause order. Unification is most
general in the selected term domain, and failure means that no solution exists
in that same domain. Thus finite and rational semantics may backtrack differently.\<close>
inductive logic_cut_step ::
  "('f logic_symbol logic_tree \<Rightarrow> bool) \<Rightarrow> 'f logic_cut_program \<Rightarrow>
    'f logic_symbol logic_tree logic_choice list \<Rightarrow>
    'f logic_symbol logic_tree logic_choice list \<Rightarrow> bool" for D P where
  admin: "logic_admin s = Some t \<Longrightarrow> logic_cut_step D P s t"
| case_call: "logic_fresh_mark m (LogicGoals (LogicAtom (LFun (LogicUser f) ts)#gs)#es) \<Longrightarrow>
    logic_cut_step D P (LogicGoals (LogicAtom (LFun (LogicUser f) ts)#gs)#es)
      (map (\<lambda>c. LogicClause (LogicAtom (LFun (LogicUser f) ts)#gs) c m)
        (logic_slice P f (length ts)) @ LogicBarrier m#es)"
| resolve: "c<length P \<Longrightarrow> logic_cut_mgu D a gs (fst (P!c)) (snd (P!c)) s r \<Longrightarrow>
    logic_cut_step D P (LogicClause (LogicAtom a#gs) c m#es)
      (LogicGoals (map (logic_bind_cut m (logic_eval r)) (snd (P!c)) @
        map (logic_goal_map (logic_subst s)) gs)#es)"
| backtrack: "c<length P \<Longrightarrow>
    \<not> (\<exists>s r. logic_substitution D s \<and> logic_substitution D r \<and>
      logic_subst s a = logic_eval r (fst (P!c))) \<Longrightarrow>
    logic_cut_step D P (LogicClause (LogicAtom a#gs) c m#es) es"
| unify: "logic_unify_mgu D a b gs s \<Longrightarrow>
    logic_cut_step D P (LogicGoals (LogicUnify a b#gs)#es)
      (LogicGoals (map (logic_goal_map (logic_subst s)) gs)#es)"
| unify_fail: "\<not> (\<exists>s. logic_substitution D s \<and> logic_subst s a = logic_subst s b) \<Longrightarrow>
    logic_cut_step D P (LogicGoals (LogicUnify a b#gs)#es) es"
| meta: "logic_fresh_mark m (LogicGoals (LogicMeta (LFun f ts)#gs)#es) \<Longrightarrow>
    logic_lower m (LFun f ts) body \<Longrightarrow>
    logic_cut_step D P (LogicGoals (LogicMeta (LFun f ts)#gs)#es)
      (LogicGoals (body@gs)#LogicBarrier m#es)"
| meta_diverges: "logic_lower_diverges a \<Longrightarrow>
    logic_cut_step D P (LogicGoals (LogicMeta a#gs)#es) (LogicGoals (LogicMeta a#gs)#es)"

text \<open>Programs have user-predicate heads. The query class uses finite terms
and the same ground/arbitrary modes as definite LP. The initial state contains
one goal and no saved alternatives.\<close>
definition logic_cut_problem where
  "logic_cut_problem P \<longleftrightarrow> (\<forall>(h,bs)\<in>set P. \<exists>f ts. h = SFun (LogicUser f) ts)"
definition logic_cut_terminates_in where
  "logic_cut_terminates_in D P p modes \<longleftrightarrow>
    \<not> (\<exists>ts s. logic_query (LogicUser p) modes (LogicUser p,ts) \<and>
      s 0 = [LogicGoals [LogicAtom (LFun (LogicUser p) (map logic_embed ts))]] \<and>
      (\<forall>n. logic_cut_step D P (s n) (s (Suc n))))"

end
